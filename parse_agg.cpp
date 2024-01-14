/* -------------------------------------------------------------------------
 *
 * parse_agg.c
 *	  handle aggregates and window functions in parser
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/common/backend/parser/parse_agg.cpp
 *
 * -------------------------------------------------------------------------
 */
#include "postgres.h"
#include "knl/knl_variable.h"

#include "catalog/pg_aggregate.h"
#include "catalog/pg_constraint.h"
#include "catalog/pg_type.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/tlist.h"
#include "parser/parse_agg.h"
#include "parser/parse_clause.h"
#include "parser/parse_coerce.h"
#include "parser/parsetree.h"
#include "parser/parse_expr.h"
#include "rewrite/rewriteManip.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#ifdef PGXC
#include "pgxc/pgxc.h"
#include "access/htup.h"
#include "catalog/pg_aggregate.h"
#include "utils/syscache.h"
#endif

/*
 * 结构体: check_ungrouped_columns_context
 * 描述: 用于检查未分组的列的上下文结构体
 */
typedef struct {
    ParseState* pstate;             // 解析状态
    Query* qry;                     // 查询节点
    PlannerInfo* root;               // 查询规划信息
    List* groupClauses;              // 分组子句列表
    List* groupClauseCommonVars;     // 分组子句的公共变量列表
    bool have_non_var_grouping;      // 是否存在非变量的分组列
    List** func_grouped_rels;        // 函数分组的关系列表
    int sublevels_up;                // 子查询层数
    bool in_agg_direct_args;         // 是否在聚合函数的直接参数中
} check_ungrouped_columns_context;

/*
 * 结构体: check_agg_arguments_context
 * 描述: 用于检查聚合参数的上下文结构体
 */
typedef struct
{
    ParseState *pstate;             // 解析状态
    int			min_varlevel;        // 最小变量层级
    int			min_agglevel;        // 最小聚合函数层级
    int			sublevels_up;        // 子查询层数
} check_agg_arguments_context;

/*
 * 函数: check_agg_arguments
 * 描述: 检查聚合函数的参数
 */
static int	check_agg_arguments(ParseState *pstate,
								List *directargs,
								List *args,
								Expr *filter);

/*
 * 函数: check_agg_arguments_walker
 * 描述: 用于遍历检查聚合参数的回调函数
 */
static bool check_agg_arguments_walker(Node *node,
									   check_agg_arguments_context *context);

/*
 * 函数: check_agglevels_and_constraints
 * 描述: 检查聚合函数的层级和约束条件
 */
static void check_agglevels_and_constraints(ParseState *pstate, Node *expr);

/*
 * 函数: check_ungrouped_columns
 * 描述: 检查未分组的列
 */
static void check_ungrouped_columns(Node* node, ParseState* pstate, Query* qry, List* groupClauses,
    List* groupClauseVars, bool have_non_var_grouping, List** func_grouped_rels);

/*
 * 函数: check_ungrouped_columns_walker
 * 描述: 用于遍历检查未分组列的回调函数
 */
static bool check_ungrouped_columns_walker(Node* node, check_ungrouped_columns_context* context);

/*
 * 函数: finalize_grouping_exprs
 * 描述: 最终化分组表达式
 */
static void finalize_grouping_exprs(
    Node* node, ParseState* pstate, Query* qry, List* groupClauses, PlannerInfo* root, bool have_non_var_grouping);

/*
 * 函数: finalize_grouping_exprs_walker
 * 描述: 用于遍历最终化分组表达式的回调函数
 */
static bool finalize_grouping_exprs_walker(Node* node, check_ungrouped_columns_context* context);

/*
 * 函数: expand_groupingset_node
 * 描述: 展开分组集节点
 */
static List* expand_groupingset_node(GroupingSet* gs);

/*
 * 函数: find_rownum_in_groupby_clauses
 * 描述: 在分组子句中查找行号变量
 */
#ifndef ENABLE_MULTIPLE_NODES
static void find_rownum_in_groupby_clauses(Rownum *rownumVar, check_ungrouped_columns_context* context);
#endif
/*
 * 函数: transformAggregateCall
 * 描述: 完成聚合调用的初始转换。
 * parse_func.c 已经识别该函数为聚合函数，并设置了 Aggref 的所有字段，除了 args、aggorder、aggdistinct 和 agglevelsup。
 * 传入的 args 列表已经通过标准表达式转换，而传入的 aggorder 列表尚未转换。
 * 在这里，我们将 args 列表转换为一个目标列表，通过插入 TargetEntry 节点，然后转换 aggorder 和 agg_distinct 规范以生成 SortGroupClause 节点的列表。
 * 这可能还会导致将 resjunk 表达式添加到目标列表中。
 * 我们还必须确定聚合实际属于哪个查询级别，相应地设置 agglevelsup，并在相应的 pstate 级别中将 p_hasAggs 标记为 true。
 */
void transformAggregateCall(ParseState* pstate, Aggref* agg, List* args, List* aggorder, bool agg_distinct)
{
#define anyenum_typeoid 3500
    List* tlist = NIL;              // 目标列表
    List* torder = NIL;             // ORDER BY 子句的转换结果
    List* tdistinct = NIL;          // DISTINCT 子句的转换结果
    AttrNumber attno = 1;           // 目标项的编号
    int save_next_resno;             // 保存原始 p_next_resno
    int min_varlevel;                // 最小变量层级
    ListCell* lc = NULL;             // List 遍历指针
#ifdef PGXC
    HeapTuple aggTuple;
    Form_pg_aggregate aggform;
#endif /* PGXC */

    if (AGGKIND_IS_ORDERED_SET(agg->aggkind)) {
        /*
         * 有序集合聚合包含直接参数和聚合参数。
         * 直接参数保存在前 "numDirectArgs" 个参数中，聚合参数保存在末尾。我们必须将它们分开。
         */
        int numDirectArgs = list_length(args) - list_length(aggorder);
        List* aargs = NIL;
        ListCell* lc1 = NULL;
        ListCell* lc2 = NULL;

        Assert(numDirectArgs >= 0);

        aargs = list_copy_tail(args, numDirectArgs);
        agg->aggdirectargs = list_truncate(args, numDirectArgs);

        /*
         * 我们应该保存有序集合聚合的排序信息，所以我们需要建立一个 tlist（通常只有一个目标项），
         * 其中包含聚合参数（Exprs 列表）。我们还需要保存相应的排序目标，以便转换为 SortGroupClause。
         */
        forboth(lc1, aargs, lc2, aggorder)
        {
            TargetEntry* tle = makeTargetEntry((Expr*)lfirst(lc1), attno++, NULL, false);
            tlist = lappend(tlist, tle);

            torder = addTargetToSortList(pstate, tle, torder, tlist, (SortBy*)lfirst(lc2), true); /* fix unknowns */
        }

        /* 有序集合聚合不能使用 DISTINCT */
        Assert(!agg_distinct);
    } else {
        /* 普通聚合没有直接参数 */
        agg->aggdirectargs = NIL;

        /*
         * 将表达式列表转换为目标列表。我们不费力为条目分配列名。
         */
        foreach (lc, args) {
            Expr* arg = (Expr*)lfirst(lc);
            TargetEntry* tle = makeTargetEntry(arg, attno++, NULL, false);
            tlist = lappend(tlist, tle);
        }

        /*
         * 如果有 ORDER BY，则进行转换。如果在 ORDER BY 中出现但在参数列表中尚不存在，它将在 tlist 中添加列。
         * 这些将标记为 resjunk = true，以便我们稍后可以将它们与常规聚合参数区分开来。
         *
         * 我们需要处理 p_next_resno，因为它将用于对任何新的目标列表条目进行编号。
         */
        save_next_resno = pstate->p_next_resno;
        pstate->p_next_resno = attno;

        pstate->shouldCheckOrderbyCol = (agg_distinct && !ALLOW_ORDERBY_UNDISTINCT_COLUMN && !IsInitdb && DB_IS_CMPT(B_FORMAT));
        torder = transformSortClause(pstate,
            aggorder,
            &tlist,
            EXPR_KIND_WINDOW_ORDER,
            true,  /* fix unknowns */
            true); /* force SQL99 rules */

        pstate->shouldCheckOrderbyCol = false;

        /*
         * 如果有 DISTINCT，则转换为产生 distinctList。
         */
        if (agg_distinct) {
            tdistinct = transformDistinctClause(pstate, &tlist, torder, true);

            /*
             * 如果将来为聚合添加对哈希去重的执行程序支持，则删除此检查。
             */
            foreach (lc, tdistinct) {
                SortGroupClause* sortcl = (SortGroupClause*)lfirst(lc);

                if (!OidIsValid(sortcl->sortop)) {
                    Node* expr = get_sortgroupclause_expr(sortcl, tlist);

                    ereport(ERROR,
                        (errcode(ERRCODE_UNDEFINED_FUNCTION),
                            errmsg(
                                "could not identify an ordering operator for type %s", format_type_be(exprType(expr))),
                            errdetail("Aggregates with DISTINCT must be able to sort their inputs."),
                            parser_errposition(pstate, exprLocation(expr))));
                }
            }
        }

        pstate->p_next_resno = save_next_resno;
    }

    /* 使用转换结果更新 Aggref */
    agg->args = tlist;
    agg->aggorder = torder;
    agg->aggdistinct = tdistinct;

    if (pstate->p_is_flt_frame) {
        check_agglevels_and_constraints(pstate, (Node*)agg);
    } else {
        /*
        * 聚合的层级与其参数中最低层次的变量或聚合的层级相同；
        * 或者如果它根本不包含变量，则我们假定它是本地的。
        */
        min_varlevel = find_minimum_var_level((Node*)agg->args);
        /*
        * 一个聚合不能直接包含相同层级的另一个聚合调用（尽管外部的聚合是可以的）。
        * 如果我们没有找到任何本地变量或聚合，我们可以跳过此检查。
        */
        if (min_varlevel == 0) {
            if (pstate->p_hasAggs && checkExprHasAggs((Node*)agg->args)) {
                ereport(ERROR,
                    (errcode(ERRCODE_GROUPING_ERROR),
                        errmsg("aggregate function calls cannot be nested"),
                        parser_errposition(pstate, locate_agg_of_level((Node*)agg->args, 0))));
            }
        }

        /* 它也不能包含返回集的函数 */
        if (checkExprHasSetReturningFuncs((Node*)agg->args)) {
            ereport(ERROR,
                (errcode(ERRCODE_GROUPING_ERROR),
                    errmsg("aggregate function calls cannot contain set-returning function calls"),
                    parser_errposition(pstate, locate_srfunc((Node*)agg->args))));
        }

        /* 它也不能包含窗口函数 */
        if (pstate->p_hasWindowFuncs && checkExprHasWindowFuncs((Node*)agg->args)) {
            ereport(ERROR,
                (errcode(ERRCODE_GROUPING_ERROR),
                    errmsg("aggregate function calls cannot contain window function calls"),
                    parser_errposition(pstate, locate_windowfunc((Node*)agg->args))));
        }

        if (min_varlevel < 0) {
            min_varlevel = 0;
        }
        agg->agglevelsup = min_varlevel;

        /* 将正确的 pstate 标记为具有聚合函数 */
        while (min_varlevel-- > 0)
            pstate = pstate->parentParseState;
        pstate->p_hasAggs = true;

        /*
        * 如果我们在聚合查询的 LATERAL 子查询中，则发出警告。
        * 我们必须在其 FROM 子句中，所以聚合放置不正确。
        */
        if (pstate->p_lateral_active)
            ereport(ERROR,
                (errcode(ERRCODE_GROUPING_ERROR),
                errmsg("aggregates not allowed in FROM clause"),
                parser_errposition(pstate, agg->location)));
    }

#ifdef PGXC
    /*
     * PGXC Datanode 的聚合函数的返回数据类型应始终返回转换函数的结果，这是协调器上集合函数预期的。
     * 查找聚合定义并替换 agg->aggtype。
     */

    aggTuple = SearchSysCache(AGGFNOID, ObjectIdGetDatum(agg->aggfnoid), 0, 0, 0);
    if (!HeapTupleIsValid(aggTuple))
        ereport(ERROR,
            (errcode(ERRCODE_CACHE_LOOKUP_FAILED), errmsg("cache lookup failed for aggregate %u", agg->aggfnoid)));
    aggform = (Form_pg_aggregate)GETSTRUCT(aggTuple);
    agg->aggtrantype = aggform->aggtranstype;
    agg->agghas_collectfn = OidIsValid(aggform->aggcollectfn);

    /*
     * 我们需要确保在视图包含 avg 函数时成功升级，否则可能会导致类似的错误：
     * operator does not exist: bigint[] = integer。
     *
     * 例如：
     *     create view t1_v as select a from t1 group by a having avg(a) = 10;
     * 对于用户定义的枚举类型，在此处不要替换 agg->aggtype，否则可能会导致错误：
     * operator does not exist: (user-defined enum type) = anyenum。
     */
    if (IS_PGXC_DATANODE && !isRestoreMode && !u_sess->catalog_cxt.Parse_sql_language && !IsInitdb &&
        !u_sess->attr.attr_common.IsInplaceUpgrade && !IS_SINGLE_NODE && (anyenum_typeoid != agg->aggtrantype))
        agg->aggtype = agg->aggtrantype;

    ReleaseSysCache(aggTuple);
#endif
}

/*
 * transformWindowFuncCall -
 *		完成窗口函数调用的初始转换
 *
 * parse_func.c 文件已经识别该函数为窗口函数，并已设置 WindowFunc 结构体的所有字段，但还未设置 winref 字段。
 * 在这里，我们需要（1）将 WindowDef 添加到 pstate 中（如果不是已经存在的窗口的重复定义），并将 winref 设置为连接到它；
 * （2）在 pstate 中标记 p_hasWindowFuncs 为 true。与聚合函数不同，只需要考虑最紧密嵌套的 pstate 级别 --- 没有“外部窗口函数”按照 SQL 规范。
 */
void transformWindowFuncCall(ParseState* pstate, WindowFunc* wfunc, WindowDef* windef)
{
    /*
     * 窗口函数调用不能包含另一个窗口函数调用（但允许包含聚合函数）。XXX
     * 这是规范要求的，还是一个未实现的特性？
     */
    if (pstate->p_hasWindowFuncs && checkExprHasWindowFuncs((Node*)wfunc->args)) {
        ereport(ERROR,
            (errcode(ERRCODE_WINDOWING_ERROR),
                errmsg("窗口函数调用不能嵌套"),
                parser_errposition(pstate, locate_windowfunc((Node*)wfunc->args))));
    }

    /*
     * 如果 OVER 子句只指定了一个窗口名称，则找到该 WINDOW 子句（最好已经存在）。否则，尝试匹配 OVER 子句的所有属性，
     * 如果没有成功，则在 p_windowdefs 列表中创建一个新条目。
     */
    if (windef->name) {
        Index winref = 0;
        ListCell* lc = NULL;

        AssertEreport(windef->refname == NULL && windef->partitionClause == NIL && windef->orderClause == NIL &&
                          windef->frameOptions == FRAMEOPTION_DEFAULTS,
            MOD_OPT,
            "");

        foreach (lc, pstate->p_windowdefs) {
            WindowDef* refwin = (WindowDef*)lfirst(lc);

            winref++;
            if (refwin->name && strcmp(refwin->name, windef->name) == 0) {
                wfunc->winref = winref;
                break;
            }
        }
        if (lc == NULL) { /* 没找到？ */
            ereport(ERROR,
                (errcode(ERRCODE_UNDEFINED_OBJECT),
                    errmsg("窗口 \"%s\" 不存在", windef->name),
                    parser_errposition(pstate, windef->location)));
        }
    } else {
        Index winref = 0;
        ListCell* lc = NULL;

        foreach (lc, pstate->p_windowdefs) {
            WindowDef* refwin = (WindowDef*)lfirst(lc);

            winref++;
            if (refwin->refname && windef->refname && strcmp(refwin->refname, windef->refname) == 0)
                /* 在 refname 上匹配 */;
            else if (!refwin->refname && !windef->refname)
                /* 匹配，没有 refname */;
            else
                continue;
            if (equal(refwin->partitionClause, windef->partitionClause) &&
                equal(refwin->orderClause, windef->orderClause) && refwin->frameOptions == windef->frameOptions &&
                equal(refwin->startOffset, windef->startOffset) && equal(refwin->endOffset, windef->endOffset)) {
                /* 找到重复的窗口规范 */
                wfunc->winref = winref;
                break;
            }
        }

        /* 没找到？ */
        if (lc == NULL) {
            pstate->p_windowdefs = lappend(pstate->p_windowdefs, windef);
            wfunc->winref = list_length(pstate->p_windowdefs);
        }
    }

    pstate->p_hasWindowFuncs = true;
}

/*
 * parseCheckAggregates
 *	检查聚合函数是否出现在不应出现的地方以及分组是否正确。
 *
 * 理想情况下，这应该在更早的阶段完成，但在语法分析层面很难区分聚合函数和普通函数。
 * 因此我们在这里进行检查。该函数应在目标列表和限定条件最终确定后调用。
 */
void parseCheckAggregates(ParseState* pstate, Query* qry)
{
    List* gset_common = NIL;
    List* groupClauses = NIL;
    List* groupClauseCommonVars = NIL;
    bool have_non_var_grouping = false;
    List* func_grouped_rels = NIL;
    ListCell* l = NULL;
    bool hasJoinRTEs = false;
    bool hasSelfRefRTEs = false;
    PlannerInfo* root = NULL;
    Node* clause = NULL;

    /* 只有在找到聚合函数或分组时才应调用此函数 */
    AssertEreport(pstate->p_hasAggs || qry->groupClause || qry->havingQual || qry->groupingSets,
        MOD_OPT,
        "只有在找到聚合函数或分组时才应调用此函数");

    /*
     * 如果存在分组集，则展开它们并找到所有集的交集。
     */
    if (qry->groupingSets) {
        /*
         * 4096 的限制是任意的，仅为避免来自病态结构的资源问题。
         */
        List* gsets = expand_grouping_sets(qry->groupingSets, 4096);

        if (gsets == NULL)
            ereport(ERROR,
                (errcode(ERRCODE_STATEMENT_TOO_COMPLEX),
                    errmsg("太多的分组集存在（最多 4096 个）"),
                    parser_errposition(pstate,
                        qry->groupClause ? exprLocation((Node*)qry->groupClause)
                                         : exprLocation((Node*)qry->groupingSets))));

        /*
         * 由于交集通常为空，因此通过使用最小的集合来初始化交集来加速交集的计算。
         */
        gset_common = (List*)linitial(gsets);

        if (gset_common != NULL) {
            for_each_cell(l, lnext(list_head(gsets))) {
                gset_common = list_intersection_int(gset_common, (List*)lfirst(l));
                if (gset_common == NULL) {
                    break;
                }
            }
        }

        /*
         * 如果扩展中只有一个分组集，并且如果 groupClause 不为空（表示分组集也不为空），
         * 那么我们可以舍弃分组集，假装我们只是普通的 GROUP BY。
         */
        if (list_length(gsets) == 1 && qry->groupClause) {
            qry->groupingSets = NIL;
        }
    }
    /*
     * 遍历范围表，看看是否有 JOIN 或自引用 CTE 条目。我们将在下面需要这些信息。
     */
    hasJoinRTEs = hasSelfRefRTEs = false;
    foreach (l, pstate->p_rtable) {
        RangeTblEntry* rte = (RangeTblEntry*)lfirst(l);

        if (rte->rtekind == RTE_JOIN) {
            hasJoinRTEs = true;
        } else if (rte->rtekind == RTE_CTE && rte->self_reference) {
            hasSelfRefRTEs = true;
        }
    }

    /*
     * 聚合函数决不能出现在 WHERE 或 JOIN/ON 子句中。
     *
     * （注意，此检查应首先出现以提供适当的错误消息；否则，我们可能会抱怨目标列表中的某个无辜的变量，
     * 如果问题在 WHERE 子句中则是完全误导的。）
     */
    if (checkExprHasAggs(qry->jointree->quals)) {
        ereport(ERROR,
            (errcode(ERRCODE_GROUPING_ERROR),
                errmsg("不允许在 WHERE 子句中使用聚合函数"),
                parser_errposition(pstate, locate_agg_of_level(qry->jointree->quals, 0))));
    }
    if (checkExprHasAggs((Node*)qry->jointree->fromlist)) { 
        ereport(ERROR,
            (errcode(ERRCODE_GROUPING_ERROR),
                errmsg("不允许在 JOIN 条件中使用聚合函数"),
                parser_errposition(pstate, locate_agg_of_level((Node*)qry->jointree->fromlist, 0))));
    }

    /*
     * GROUP BY 子句中也不允许使用聚合函数。
     *
     * 在此过程中，构建一个可接受的 GROUP BY 表达式列表，以供 check_ungrouped_columns() 使用。
     */
    foreach (l, qry->groupClause) {
        SortGroupClause* grpcl = (SortGroupClause*)lfirst(l);
        TargetEntry* expr = NULL;

        expr = get_sortgroupclause_tle(grpcl, qry->targetList);
        if (expr == NULL) {
            continue; /* 可能不会发生 */
        }
        if (checkExprHasAggs((Node*)expr->expr)) {
            ereport(ERROR,
                (errcode(ERRCODE_GROUPING_ERROR),
                    errmsg("不允许在 GROUP BY 子句中使用聚合函数"),
                    parser_errposition(pstate, locate_agg_of_level((Node*)expr->expr, 0))));
        }
        groupClauses = lcons(expr, groupClauses);
    }

    /*
     * 如果涉及联接别名变量，我们必须将它们展平为底层变量，以便别名和非别名变量将被正确视为相等。
     * 如果没有 RTE_JOIN 类型的 rangetable 条目，则可以跳过此操作的开销。我们使用规划器的 flatten_join_alias_vars 函数来执行展平；
     * 它需要一个 PlannerInfo 根节点，它幸运地可以是一个几乎是虚拟的根节点。
     */
    if (hasJoinRTEs) {
        root = makeNode(PlannerInfo);
        root->parse = qry;
        root->planner_cxt = CurrentMemoryContext;
        root->hasJoinRTEs = true;

        groupClauses = (List*)flatten_join_alias_vars(root, (Node*)groupClauses);
    } else
        root = NULL; /* 保持编译器安静 */

    /*
     * 检测分组表达式中是否有任何不是简单 Var 的情况；如果都是 Var，那么我们在递归扫描中不必那么努力。
     * （注意我们必须在此之前展开别名。）
     *
     * 跟踪包含在所有分组集中的 Var 分开，以便我们可以用它们来检查函数依赖性。
     */
    have_non_var_grouping = false;
    foreach (l, groupClauses) {
        TargetEntry* tle = (TargetEntry*)lfirst(l);
        if (!IsA(tle->expr, Var)) {
            have_non_var_grouping = true;
        } else if (!qry->groupingSets || list_member_int(gset_common, tle->ressortgroupref)) {
            groupClauseCommonVars = lappend(groupClauseCommonVars, tle->expr);
        }
    }

    /*
     * 检查目标列表和 HAVING 子句中的未分组变量。
     *
     * 注意：因为我们检查 resjunk tlist 元素以及常规元素，因此这也将找到来自 ORDER BY 和 WINDOW 子句的未分组变量。
     * 实际上，它还将检查分组表达式本身，但是它们都将通过测试......
     *
     * 我们还完成 GROUPING 表达式的检查，但是为此我们需要遍历原始（未展平）子句以修改节点。
     */
    clause = (Node*)qry->targetList;
    finalize_grouping_exprs(clause, pstate, qry, groupClauses, root, have_non_var_grouping);
    if (hasJoinRTEs) {
        clause = flatten_join_alias_vars(root, clause);
    }
    check_ungrouped_columns(
        clause, pstate, qry, groupClauses, groupClauseCommonVars, have_non_var_grouping, &func_grouped_rels);

    clause = (Node*)qry->havingQual;
    finalize_grouping_exprs(clause, pstate, qry, groupClauses, root, have_non_var_grouping);
    if (hasJoinRTEs) {
        clause = flatten_join_alias_vars(root, clause);
    }
    check_ungrouped_columns(
        clause, pstate, qry, groupClauses, groupClauseCommonVars, have_non_var_grouping, &func_grouped_rels);

    /*
     * 根据规范，聚合函数不能出现在递归项中。
     */
    if (pstate->p_hasAggs && hasSelfRefRTEs) {
        ereport(ERROR,
            (errcode(ERRCODE_INVALID_RECURSION),
                errmsg("不允许在递归查询的递归项中使用聚合函数"),
                parser_errposition(pstate, locate_agg_of_level((Node*)qry, 0))));
    }
}


/*
 * parseCheckWindowFuncs
 * 检查不应出现窗口函数的位置。
 *
 * 我们必须禁止在 WHERE、JOIN/ON、HAVING、GROUP BY 和窗口规范中使用窗口函数。
 * （其他子句，如 RETURNING 和 LIMIT，已经进行了检查。）所有这些子句的转换必须已经完成。
 */
void parseCheckWindowFuncs(ParseState* pstate, Query* qry)
{
    ListCell* l = NULL;

    /* 只有在找到窗口函数时才应调用此函数 */
    AssertEreport(pstate->p_hasWindowFuncs, MOD_OPT, "仅处理 WindowFuncs");

    if (checkExprHasWindowFuncs(qry->jointree->quals)) {
        ereport(ERROR,
            (errcode(ERRCODE_WINDOWING_ERROR),
                errmsg("不允许在 WHERE 子句中使用窗口函数"),
                parser_errposition(pstate, locate_windowfunc(qry->jointree->quals))));
    }
    if (checkExprHasWindowFuncs((Node*)qry->jointree->fromlist)) {
        ereport(ERROR,
            (errcode(ERRCODE_WINDOWING_ERROR),
                errmsg("不允许在 JOIN 条件中使用窗口函数"),
                parser_errposition(pstate, locate_windowfunc((Node*)qry->jointree->fromlist))));
    }
    if (checkExprHasWindowFuncs(qry->havingQual)) {
        ereport(ERROR,
            (errcode(ERRCODE_WINDOWING_ERROR),
                errmsg("不允许在 HAVING 子句中使用窗口函数"),
                parser_errposition(pstate, locate_windowfunc(qry->havingQual))));
    }

    foreach (l, qry->groupClause) {
        SortGroupClause* grpcl = (SortGroupClause*)lfirst(l);
        Node* expr = NULL;

        expr = get_sortgroupclause_expr(grpcl, qry->targetList);
        if (checkExprHasWindowFuncs(expr)) {
            ereport(ERROR,
                (errcode(ERRCODE_WINDOWING_ERROR),
                    errmsg("不允许在 GROUP BY 子句中使用窗口函数"),
                    parser_errposition(pstate, locate_windowfunc(expr))));
        }
    }

    foreach (l, qry->windowClause) {
        WindowClause* wc = (WindowClause*)lfirst(l);
        ListCell* l2 = NULL;

        foreach (l2, wc->partitionClause) {
            SortGroupClause* grpcl = (SortGroupClause*)lfirst(l2);
            Node* expr = NULL;

            expr = get_sortgroupclause_expr(grpcl, qry->targetList);
            if (checkExprHasWindowFuncs(expr)) {
                ereport(ERROR,
                    (errcode(ERRCODE_WINDOWING_ERROR),
                        errmsg("不允许在窗口定义中使用窗口函数"),
                        parser_errposition(pstate, locate_windowfunc(expr))));
            }
        }
        foreach (l2, wc->orderClause) {
            SortGroupClause* grpcl = (SortGroupClause*)lfirst(l2);
            Node* expr = NULL;

            expr = get_sortgroupclause_expr(grpcl, qry->targetList);
            if (checkExprHasWindowFuncs(expr)) {
                ereport(ERROR,
                    (errcode(ERRCODE_WINDOWING_ERROR),
                        errmsg("不允许在窗口定义中使用窗口函数"),
                        parser_errposition(pstate, locate_windowfunc(expr))));
            }
        }
        /* startOffset 和 limitOffset 在 transformFrameOffset 中已检查 */
    }
}


/*
 * Aggregate functions and grouping operations (which are combined in the spec
 * as <set function specification>) are very similar with regard to level and
 * nesting restrictions (though we allow a lot more things than the spec does).
 * Centralize those restrictions here.
 */
static void check_agglevels_and_constraints(ParseState *pstate, Node *expr)
{
    List       *directargs = NIL;
    List       *args = NIL;
    Expr       *filter = NULL;
    int         min_varlevel;
    int         location = -1;
    Index      *p_levelsup;
    const char *err;
    bool        errkind;
    bool        isAgg = IsA(expr, Aggref);

    if (isAgg)
    {
        Aggref    *agg = (Aggref *) expr;

        directargs = agg->aggdirectargs;
        args = agg->args;
        location = agg->location;
        p_levelsup = &agg->agglevelsup;
    }
    else
    {
        GroupingFunc *grp = (GroupingFunc *) expr;

        args = grp->args;
        location = grp->location;
        p_levelsup = &grp->agglevelsup;
    }

    /*
     * Check the arguments to compute the aggregate's level and detect
     * improper nesting.
     */
    min_varlevel = check_agg_arguments(pstate,
                                       directargs,
                                       args,
                                       filter);

    *p_levelsup = min_varlevel;

    /* Mark the correct pstate level as having aggregates */
    while (min_varlevel-- > 0)
        pstate = pstate->parentParseState;
    pstate->p_hasAggs = true;

    /*
     * Check to see if the aggregate function is in an invalid place within
     * its aggregation query.
     *
     * For brevity, we support two schemes for reporting an error here: set
     * "err" to a custom message, or set "errkind" true if the error context
     * is sufficiently identified by what ParseExprKindName will return, *and*
     * what it will return is just a SQL keyword.  (Otherwise, use a custom
     * message to avoid creating translation problems.)
     */
    err = NULL;
    errkind = false;
	switch (pstate->p_expr_kind)
    {
        case EXPR_KIND_NONE:
            Assert(false);     /* 不应该发生 */
            break;
        case EXPR_KIND_OTHER:

            /*
            * 在这里接受聚合和分组操作；调用方必须在需要时引发错误
            */
            break;
        case EXPR_KIND_JOIN_ON:
        case EXPR_KIND_JOIN_USING:
            if (isAgg)
                err = _("聚合函数不允许出现在JOIN条件中");
            else
                err = _("分组操作不允许出现在JOIN条件中");
            break;
        case EXPR_KIND_FROM_SUBSELECT:
            /* 应该只在LATERAL子查询中出现 */
            Assert(pstate->p_lateral_active);

            /*
            * 聚合/分组范围规则使得在此处明确是值得的
            */
            if (isAgg)
                err = _("聚合函数不允许出现在其自己查询级别的FROM子句中");
            else
                err = _("分组操作不允许出现在其自己查询级别的FROM子句中");
            break;
        case EXPR_KIND_FROM_FUNCTION:
            if (isAgg)
                err = _("聚合函数不允许出现在FROM子句中的函数中");
            else
                err = _("分组操作不允许出现在FROM子句中的函数中");
            break;
        case EXPR_KIND_WHERE:
            errkind = true;
            break;
        case EXPR_KIND_POLICY:
            if (isAgg)
                err = _("聚合函数不允许出现在策略表达式中");
            else
                err = _("分组操作不允许出现在策略表达式中");
            break;
        case EXPR_KIND_HAVING:
            /* 可以 */
            break;
        case EXPR_KIND_FILTER:
            errkind = true;
            break;
        case EXPR_KIND_WINDOW_PARTITION:
            /* 可以 */
            break;
        case EXPR_KIND_WINDOW_ORDER:
            /* 可以 */
            break;
        case EXPR_KIND_WINDOW_FRAME_RANGE:
            if (isAgg)
                err = _("聚合函数不允许出现在窗口RANGE中");
            else
                err = _("分组操作不允许出现在窗口RANGE中");
            break;
        case EXPR_KIND_WINDOW_FRAME_ROWS:
            if (isAgg)
                err = _("聚合函数不允许出现在窗口ROWS中");
            else
                err = _("分组操作不允许出现在窗口ROWS中");
            break;
        case EXPR_KIND_WINDOW_FRAME_GROUPS:
            if (isAgg)
                err = _("聚合函数不允许出现在窗口GROUPS中");
            else
                err = _("分组操作不允许出现在窗口GROUPS中");
            break;
        case EXPR_KIND_SELECT_TARGET:
            /* 可以 */
            break;
        case EXPR_KIND_INSERT_TARGET:
        case EXPR_KIND_UPDATE_SOURCE:
        case EXPR_KIND_UPDATE_TARGET:
            errkind = true;
            break;
        case EXPR_KIND_MERGE_WHEN:
            if (isAgg)
                err = _("聚合函数不允许出现在MERGE WHEN条件中");
            else
                err = _("分组操作不允许出现在MERGE WHEN条件中");
            break;
        case EXPR_KIND_GROUP_BY:
            errkind = true;
            break;
        case EXPR_KIND_ORDER_BY:
            /* 可以 */
            break;
        case EXPR_KIND_DISTINCT_ON:
            /* 可以 */
            break;
        case EXPR_KIND_LIMIT:
        case EXPR_KIND_OFFSET:
            errkind = true;
            break;
        case EXPR_KIND_RETURNING:
            errkind = true;
            break;
        case EXPR_KIND_VALUES:
        case EXPR_KIND_VALUES_SINGLE:
            errkind = true;
            break;
        case EXPR_KIND_CHECK_CONSTRAINT:
        case EXPR_KIND_DOMAIN_CHECK:
            if (isAgg)
                err = _("聚合函数不允许出现在检查约束中");
            else
                err = _("分组操作不允许出现在检查约束中");
            break;
        case EXPR_KIND_COLUMN_DEFAULT:
        case EXPR_KIND_FUNCTION_DEFAULT:
            if (isAgg)
                err = _("聚合函数不允许出现在DEFAULT表达式中");
            else
                err = _("分组操作不允许出现在DEFAULT表达式中");
            break;
        case EXPR_KIND_INDEX_EXPRESSION:
            if (isAgg)
                err = _("聚合函数不允许出现在索引表达式中");
            else
                err = _("分组操作不允许出现在索引表达式中");
            break;
        case EXPR_KIND_INDEX_PREDICATE:
            if (isAgg)
                err = _("聚合函数不允许出现在索引谓词中");
            else
                err = _("分组操作不允许出现在索引谓词中");
            break;
        case EXPR_KIND_STATS_EXPRESSION:
            if (isAgg)
                err = _("聚合函数不允许出现在统计表达式中");
            else
                err = _("分组操作不允许出现在统计表达式中");
            break;
        case EXPR_KIND_ALTER_COL_TRANSFORM:
            if (isAgg)
                err = _("聚合函数不允许出现在变换表达式中");
            else
                err = _("分组操作不允许出现在变换表达式中");
            break;
        case EXPR_KIND_EXECUTE_PARAMETER:
            if (isAgg)
                err = _("聚合函数不允许出现在EXECUTE参数中");
            else
                err = _("分组操作不允许出现在EXECUTE参数中");
            break;
        case EXPR_KIND_TRIGGER_WHEN:
            if (isAgg)
                err = _("聚合函数不允许出现在触发器WHEN条件中");
            else
                err = _("分组操作不允许出现在触发器WHEN条件中");
            break;
        case EXPR_KIND_PARTITION_BOUND:
            if (isAgg)
                err = _("聚合函数不允许出现在分区边界中");
            else
                err = _("分组操作不允许出现在分区边界中");
            break;
        case EXPR_KIND_PARTITION_EXPRESSION:
            if (isAgg)
                err = _("聚合函数不允许出现在分区键表达式中");
            else
                err = _("分组操作不允许出现在分区键表达式中");
            break;
        case EXPR_KIND_GENERATED_COLUMN:
            if (isAgg)
                err = _("聚合函数不允许出现在生成列表达式中");
            else
                err = _("分组操作不允许出现在生成列表达式中");
            break;
        case EXPR_KIND_CALL_ARGUMENT:
            if (isAgg)
                err = _("聚合函数不允许出现在CALL参数中");
            else
                err = _("分组操作不允许出现在CALL参数中");
            break;
        case EXPR_KIND_COPY_WHERE:
            if (isAgg)
                err = _("聚合函数不允许出现在COPY FROM WHERE条件中");
            else
                err = _("分组操作不允许出现在COPY FROM WHERE条件中");
            break;
        case EXPR_KIND_CYCLE_MARK:
            errkind = true;
            break;

        /*
        * 这里故意没有default: case，以便如果我们添加新的ParseExprKind而没有扩展此开关，编译器将发出警告。
        * 如果在运行时看到无法识别的值，则行为将与EXPR_KIND_OTHER相同，这是合理的。
        */
    }

    if (err)
        ereport(ERROR,
                (errcode(ERRCODE_GROUPING_ERROR),
                errmsg_internal("%s", err),
                parser_errposition(pstate, location)));

    if (errkind)
    {
        if (isAgg)
            /* 翻译器：%s是SQL构造的名称，例如GROUP BY */
            err = _("聚合函数不允许出现在%s中");
        else
            /* 翻译器：%s是SQL构造的名称，例如GROUP BY */
            err = _("分组操作不允许出现在%s中");

        ereport(ERROR,
            (errcode(ERRCODE_GROUPING_ERROR),
             errmsg_internal(err,
                             ParseExprKindName(pstate->p_expr_kind)),
             parser_errposition(pstate, location)));
    }

}
/*
 * check_agg_arguments
 *	  扫描聚合函数的参数，确定聚合的语义级别（零是当前选择的级别，一是其父级别等）。
 *
 * 聚合的级别与其聚合参数（包括任何 ORDER BY 列）或过滤表达式中最低级别的变量或聚合的级别相同；
 * 或者如果它根本不包含变量，则我们假设它是本地的。
 *
 * 直接参数中的变量/聚合不计入确定聚合级别的变量，因为这些参数不是每行计算一次，而只在每组计算一次，
 * 因此在某种程度上实际上不是真正的聚合参数。然而，这可能意味着我们在直接参数中包含较低级别的变量/聚合时，
 * 仍然决定该聚合是上级级别，这种情况必须被禁止。（这有点奇怪，但是 SQL 标准似乎非常明确，直接参数不应考虑设置聚合的级别。）
 *
 * 我们还利用这个机会检测参数中的任何聚合函数或窗口函数。如果发现窗口函数，我们可以立即引发错误。
 * 对于聚合函数，情况略微复杂，因为只有在内部聚合与外部聚合的语义级别相同时才会出错，
 * 而我们直到完成扫描参数后才能知道这一点。
 */
static int
check_agg_arguments(ParseState *pstate,
                    List *directargs,
                    List *args,
                    Expr *filter)
{
    int         agglevel;
    check_agg_arguments_context context;

    context.pstate = pstate;
    context.min_varlevel = -1; /* 表示尚未找到任何内容 */
    context.min_agglevel = -1;
    context.sublevels_up = 0;

    (void) check_agg_arguments_walker((Node *) args, &context);
    (void) check_agg_arguments_walker((Node *) filter, &context);

    /*
     * 如果我们找不到变量或聚合，那么它是级别零的聚合；否则，它的级别是变量或聚合的最小级别。
     */
    if (context.min_varlevel < 0)
    {
        if (context.min_agglevel < 0)
            agglevel = 0;
        else
            agglevel = context.min_agglevel;
    }
    else if (context.min_agglevel < 0)
        agglevel = context.min_varlevel;
    else
        agglevel = Min(context.min_varlevel, context.min_agglevel);

    /*
     * 如果存在相同语义级别的嵌套聚合，请发出警告。
     */
    if (agglevel == context.min_agglevel)
    {
        int         aggloc;

        aggloc = locate_agg_of_level((Node *) args, agglevel);
        if (aggloc < 0)
            aggloc = locate_agg_of_level((Node *) filter, agglevel);
        ereport(ERROR,
                (errcode(ERRCODE_GROUPING_ERROR),
                    errmsg("aggregate function calls cannot be nested"),
                    parser_errposition(pstate, aggloc)));
    }

    /*
     * 现在检查直接参数中的变量/聚合，并在需要时引发错误。
     * 注意，我们允许将聚合的语义级别视为变量，但不允许将该级别的聚合视为变量。
     * 在原则上，这种情况可能是可以支持的，但它会在执行时在聚合之间创建排序依赖关系。
     * 由于该案例既未被规范要求也不是特别有用，我们将其视为嵌套聚合情况。
     */
    if (directargs)
    {
        context.min_varlevel = -1;
        context.min_agglevel = -1;
        (void) check_agg_arguments_walker((Node *) directargs, &context);
        if (context.min_varlevel >= 0 && context.min_varlevel < agglevel)
            ereport(ERROR,
                    (errcode(ERRCODE_GROUPING_ERROR),
                        errmsg("outer-level aggregate cannot contain a lower-level variable in its direct arguments"),
                        parser_errposition(pstate,
                                        locate_var_of_level((Node *) directargs,
                                                            context.min_varlevel))));
        if (context.min_agglevel >= 0 && context.min_agglevel <= agglevel)
            ereport(ERROR,
                    (errcode(ERRCODE_GROUPING_ERROR),
                        errmsg("aggregate function calls cannot be nested"),
                        parser_errposition(pstate,
                                        locate_agg_of_level((Node *) directargs,
                                                            context.min_agglevel))));
    }
    return agglevel;
}

/*
 * check_agg_arguments_walker
 *	  递归遍历表达式树，查找变量和聚合，并确定它们的语义级别。
 */
static bool check_agg_arguments_walker(Node* node, check_agg_arguments_context* context)
{
    if (node == NULL)
        return false;
    if (IsA(node, Var))
    {
        int varlevelsup = ((Var*)node)->varlevelsup;

        /* 将 levelsup 转换为原始查询的参照框架 */
        varlevelsup -= context->sublevels_up;
        /* 忽略子查询的本地变量 */
        if (varlevelsup >= 0)
        {
            if (context->min_varlevel < 0 || context->min_varlevel > varlevelsup)
                context->min_varlevel = varlevelsup;
        }
        return false;
    }
    if (IsA(node, Aggref))
    {
        int agglevelsup = ((Aggref*)node)->agglevelsup;

        /* 将 levelsup 转换为原始查询的参照框架 */
        agglevelsup -= context->sublevels_up;
        /* 忽略子查询的本地聚合 */
        if (agglevelsup >= 0)
        {
            if (context->min_agglevel < 0 || context->min_agglevel > agglevelsup)
                context->min_agglevel = agglevelsup;
        }
        /* 不需要检查内部聚合的参数 */
        return false;
    }
    if (IsA(node, GroupingFunc))
    {
        int agglevelsup = ((GroupingFunc*)node)->agglevelsup;

        /* 将 levelsup 转换为原始查询的参照框架 */
        agglevelsup -= context->sublevels_up;
        /* 忽略子查询的本地聚合 */
        if (agglevelsup >= 0)
        {
            if (context->min_agglevel < 0 || context->min_agglevel > agglevelsup)
                context->min_agglevel = agglevelsup;
        }
        /* 继续并进入子树 */
    }

    /*
     * 立即拒绝 SRF 和窗口函数，除非我们在聚合的参数中的子查询中；在这种情况下，它们是可以接受的。
     */
    if (context->sublevels_up == 0)
    {
        if ((IsA(node, FuncExpr) && ((FuncExpr*)node)->funcretset) ||
            (IsA(node, OpExpr) && ((OpExpr*)node)->opretset))
            ereport(ERROR,
                (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                    errmsg("aggregate function calls cannot contain set-returning function calls"),
                    parser_errposition(context->pstate, exprLocation(node))));
        if (IsA(node, WindowFunc))
            ereport(ERROR,
                (errcode(ERRCODE_GROUPING_ERROR),
                    errmsg("aggregate function calls cannot contain window function calls"),
                    parser_errposition(context->pstate, ((WindowFunc*)node)->location)));
    }
    if (IsA(node, Query))
    {
        /* 递归到子查询中 */
        bool result;

        context->sublevels_up++;
        result = query_tree_walker((Query*)node,
            (bool (*)())check_agg_arguments_walker,
            (void*)context,
            0);
        context->sublevels_up--;
        return result;
    }

    return expression_tree_walker(node,
        (bool (*)())check_agg_arguments_walker,
        (void*)context);
}

/*
 * check_ungrouped_columns
 *		扫描给定的表达式树，查找未在 groupClauses 列表中列出的未分组变量
 *		(既不在 groupClauses 中，也不在聚合函数的参数中)。
 *		如果发现任何未分组变量，则发出合适的错误消息。
 *
 * 注意：我们假设给定的子句已经经过了适当的转换以用于解析器输出。
 *
 * 注意：我们在主查询中识别分组表达式，但仅在子查询中识别分组变量。
 * 例如，尽管可能允许：
 *		SELECT
 *			(SELECT x FROM bar where y = (foo.a + foo.b))
 *		FROM foo
 *		GROUP BY a + b;
 * 但是这会被拒绝，尽管这是可以允许的。
 * 难点在于需要考虑到不同的 sublevels_up。
 * 这似乎需要 equal() 的整个定制版本，这比功能的价值要高得多。
 */
static void check_ungrouped_columns(Node* node, ParseState* pstate, Query* qry, List* groupClauses,
    List* groupClauseCommonVars, bool have_non_var_grouping, List** func_grouped_rels)
{
    check_ungrouped_columns_context context;

    context.pstate = pstate;
    context.qry = qry;
    context.root = NULL;
    context.groupClauses = groupClauses;
    context.groupClauseCommonVars = groupClauseCommonVars;
    context.have_non_var_grouping = have_non_var_grouping;
    context.func_grouped_rels = func_grouped_rels;
    context.sublevels_up = 0;
    context.in_agg_direct_args = false;
    (void)check_ungrouped_columns_walker(node, &context);
}

/*
 * check_ungrouped_columns_walker
 *   - 递归遍历查询表达式树，检查是否存在未在GROUP BY子句中列出的未分组变量。
 */
static bool check_ungrouped_columns_walker(Node* node, check_ungrouped_columns_context* context)
{
    ListCell* gl = NULL;

    if (node == NULL) {
        return false;
    }
    if (IsA(node, Const) || IsA(node, Param)) {
        return false; /* 常量始终是可以接受的 */
    }

    if (IsA(node, Aggref)) {
        Aggref* agg = (Aggref*)node;

        if ((int)agg->agglevelsup == context->sublevels_up) {
            /*
             * 对于有序集聚合函数，其直接参数不应该在另一个聚合函数内部。如果我们发现原始级别的聚合函数调用
             * （也就是说，如果它在外部查询中，上下文应该是相同的），则不要递归到其普通参数、ORDER BY参数或
             * 过滤器中；在那里未分组的变量不是一个错误。我们在上下文中使用in_agg_direct_args来帮助生成有关
             * 直接参数中未分组变量的有用错误消息。
             */
            bool result = false;

            if (context->in_agg_direct_args) {
                ereport(ERROR, (errcode(ERRCODE_INVALID_AGG), errmsg("unexpected args inside agg direct args")));
            }
            context->in_agg_direct_args = true;
            result = check_ungrouped_columns_walker((Node*)agg->aggdirectargs, context);
            context->in_agg_direct_args = false;
            return result;
        }

        /*
         * 我们还可以跳过更高级别的聚合函数的参数，因为它们不可能包含对我们有影响的变量（参见transformAggregateCall）。
         * 但是，我们确实需要查看更低级别的聚合函数的参数。
         */
        if ((int)agg->agglevelsup > context->sublevels_up) {
            return false;
        }
    }

    if (IsA(node, GroupingFunc)) {
        GroupingFunc* grp = (GroupingFunc*)node;

        /* 单独处理GroupingFunc，此级别上的不需要重新检查 */
        if ((int)grp->agglevelsup >= context->sublevels_up) {
            return false;
        }
    }

    /*
     * 如果我们有任何不是简单变量的GROUP BY项，请查看整个子表达式是否与任何GROUP BY项匹配。
     * 我们需要在每个递归级别都这样做，以便在达到其中的变量之前就识别GROUPed-BY表达式。
     * 但是，这仅在外部查询级别上有效，如上所述。
     */
    if (context->have_non_var_grouping && context->sublevels_up == 0) {
        foreach (gl, context->groupClauses) {
            TargetEntry* tle = (TargetEntry*)lfirst(gl);
            if (equal(node, tle->expr)) {
                return false; /* 可以接受，不需要更深入递归 */
            }
        }
    }

#ifndef ENABLE_MULTIPLE_NODES
    /* 如果有ROWNUM，它必须出现在GROUP BY子句中或在聚合函数中使用。 */
    if (IsA(node, Rownum) && context->sublevels_up == 0) {
        find_rownum_in_groupby_clauses((Rownum *)node, context);
    }
#endif

    /*
     * 如果我们有一个未分组的原始查询级别的变量，那么我们有一个错误。原始查询级别以下的变量不是问题，
     * 原始查询级别以上的变量也不是问题。 （如果这些变量在其自己的查询级别上是未分组的，那是别人的问题...）
     */
    if (IsA(node, Var)) {
        Var* var = (Var*)node;
        RangeTblEntry* rte = NULL;
        char* attname = NULL;

        if (var->varlevelsup != (unsigned int)context->sublevels_up) {
            return false; /* 它不是本地查询的，忽略 */
        }

        /*
         * 检查匹配，如果我们在上面没有做的话。
         */
        if (!context->have_non_var_grouping || context->sublevels_up != 0) {
            foreach (gl, context->groupClauses) {
                Var* gvar = (Var*)((TargetEntry*)lfirst(gl))->expr;

                if (IsA(gvar, Var) && gvar->varno == var->varno && gvar->varattno == var->varattno &&
                    gvar->varlevelsup == 0)
                    return false; /* 可以接受，我们没问题 */
            }
        }

        /*
         * 检查变量是否在GROUP BY列上功能依赖。如果是这样，我们可以允许使用变量，因为对于该表，分组实际上是无效的。
         * 但是，这个推导依赖于表的一个或多个约束，因此我们必须将这些约束添加到查询的constraintDeps列表中，
         * 因为如果约束被删除，它就不再有语义上的有效性。
         * （因此，这个检查必须是在提高错误之前的最后的努力：我们不希望不必要地添加依赖。）
         *
         * 由于这是一个相当昂贵的检查，并且对于表的所有列都会有相同的结果，我们在func_grouped_rels列表中记住了我们已经
         * 证明功能依赖关系的RTEs。此测试还防止我们将重复的条目添加到constraintDeps列表中。
         */
        if (list_member_int(*context->func_grouped_rels, var->varno)) {
            return false; /* 先前已被证明是可以接受的 */
        }

        AssertEreport(
            var->varno > 0 && (int)var->varno <= list_length(context->pstate->p_rtable), MOD_OPT, "Var is unexpected");
        rte = rt_fetch(var->varno, context->pstate->p_rtable);
        if (rte->rtekind == RTE_RELATION) {
            if (check_functional_grouping(
                    rte->relid, var->varno, 0, context->groupClauseCommonVars, &context->qry->constraintDeps)) {
                *context->func_grouped_rels = lappend_int(*context->func_grouped_rels, var->varno);
                return false; /* 可以接受 */
            }
        }

        /* 找到了未分组的本地变量；生成错误消息 */
        attname = get_rte_attribute_name(rte, var->varattno);

        /* 如果RTE已经被start with...connect by重写，则修复attname。 */
        char* orig_attname = attname;
        if (IsSWCBRewriteRTE(rte)) {
            attname = strrchr(attname, '@');
            attname = (attname != NULL) ? (attname + 1) : orig_attname;
        }

        if (context->sublevels_up == 0) {
            ereport(ERROR,
                (errcode(ERRCODE_GROUPING_ERROR),
                    errmsg("column \"%s.%s\" must appear in the GROUP BY clause or be used in an aggregate function",
                        rte->eref->aliasname,
                        attname),
                    context->in_agg_direct_args
                        ? errdetail("Direct arguments of an ordered-set aggregate must use only grouped columns.")
                        : 0,
                    rte->swConverted ? errdetail("Please check your start with rewrite table's column.") : 0,
                    parser_errposition(context->pstate, var->location)));
        } else {
            ereport(ERROR,
                (errcode(ERRCODE_GROUPING_ERROR),
                    errmsg("subquery uses ungrouped column \"%s.%s\" from outer query", rte->eref->aliasname, attname),
                    parser_errposition(context->pstate, var->location)));
        }
        if (attname != NULL) {
            pfree_ext(attname);
        }
    }

    if (IsA(node, Query)) {
        /* 递归到子查询中 */
        bool result = false;

        context->sublevels_up++;
        result = query_tree_walker((Query*)node, (bool (*)())check_ungrouped_columns_walker, (void*)context, 0);
        context->sublevels_up--;
        return result;
    }
    return expression_tree_walker(node, (bool (*)())check_ungrouped_columns_walker, (void*)context);
}

/*
 * finalize_grouping_exprs -
 *	  从给定的表达式树中扫描GROUPING()和相关调用，
 *	  验证并处理它们的参数。
 *
 * 这个函数从check_ungrouped_columns中拆分出来，因为它需要修改节点
 * （它是原地修改，而不是通过变异器），而check_ungrouped_columns可能只
 * 看到原始的拷贝，由于联接别名变量的平铺。因此，在这里，我们在比较之前
 * 平铺每个单独的GROUPING参数。
 */
static void finalize_grouping_exprs(
    Node* node, ParseState* pstate, Query* qry, List* groupClauses, PlannerInfo* root, bool have_non_var_grouping)
{
    check_ungrouped_columns_context context;

    context.pstate = pstate;
    context.qry = qry;
    context.root = root;
    context.groupClauses = groupClauses;
    context.groupClauseCommonVars = NIL;
    context.have_non_var_grouping = have_non_var_grouping;
    context.func_grouped_rels = NULL;
    context.sublevels_up = 0;
    context.in_agg_direct_args = false;
    (void)finalize_grouping_exprs_walker(node, &context);
}

static bool finalize_grouping_exprs_walker(Node* node, check_ungrouped_columns_context* context)
{
    ListCell* gl = NULL;

    if (node == NULL) {
        return false;
    }
    if (IsA(node, Const) || IsA(node, Param)) {
        return false; /* 常量始终是可接受的 */
    }

    if (IsA(node, Aggref)) {
        Aggref* agg = (Aggref*)node;

        if ((int)agg->agglevelsup == context->sublevels_up) {
            /*
             * 如果我们找到原始级别的聚合调用，不要递归到其普通参数、
             * ORDER BY参数或过滤器中；这个级别不允许GROUPING表达式。
             * 但是检查直接参数，就好像它们不在聚合函数中。
             */
            bool result = false;

            AssertEreport(!context->in_agg_direct_args, MOD_OPT, "");
            context->in_agg_direct_args = true;
            result = finalize_grouping_exprs_walker((Node*)agg->aggdirectargs, context);
            context->in_agg_direct_args = false;
            return result;
        }

        /*
         * 我们可以跳过对更高级别聚合的递归，因为它们不可能包含
         * 我们关心的表达式（参见transformAggregateCall）。但是，我们确实需要
         * 查看较低级别的聚合。
         */
        if ((int)agg->agglevelsup > context->sublevels_up) {
            return false;
        }
    }

    if (IsA(node, GroupingFunc)) {
        GroupingFunc* grp = (GroupingFunc*)node;

        /*
         * 我们只需要在它们属于的确切级别检查GroupingFunc节点，因为它们不能混合级别。
         */
        if ((int)grp->agglevelsup == context->sublevels_up) {
            ListCell* lc = NULL;
            List* ref_list = NIL;

            foreach (lc, grp->args) {
                Node* expr = (Node*)lfirst(lc);
                Index ref = 0;

                if (context->root != NULL) {
                    expr = flatten_join_alias_vars(context->root, expr);
                }

                /*
                 * 每个表达式必须匹配当前查询级别的分组条目。与一般表达式情况不同，我们不允许
                 * 函数依赖关系或外部引用。
                 */
                if (IsA(expr, Var)) {
                    Var* var = (Var*)expr;

                    if ((int)var->varlevelsup == context->sublevels_up) {
                        foreach (gl, context->groupClauses) {
                            TargetEntry* tle = (TargetEntry*)lfirst(gl);
                            Var* gvar = (Var*)tle->expr;

                            if (IsA(gvar, Var) && gvar->varno == var->varno && gvar->varattno == var->varattno &&
                                gvar->varlevelsup == 0) {
                                ref = tle->ressortgroupref;
                                break;
                            }
                        }
                    }
                } else if (context->have_non_var_grouping && context->sublevels_up == 0) {
                    foreach (gl, context->groupClauses) {
                        TargetEntry* tle = (TargetEntry*)lfirst(gl);

                        if (equal(expr, tle->expr)) {
                            ref = tle->ressortgroupref;
                            break;
                        }
                    }
                }

                if (ref == 0) {
                    ereport(ERROR,
                        (errcode(ERRCODE_GROUPING_ERROR),
                            errmsg("GROUPING的参数必须是关联查询级别的分组表达式"),
                            parser_errposition(context->pstate, exprLocation(expr))));
                }

                ref_list = lappend_int(ref_list, ref);
            }

            grp->refs = ref_list;
        }

        if ((int)grp->agglevelsup > context->sublevels_up) {
            return false;
        }
    }

    if (IsA(node, Query)) {
        /* 递归到子查询中 */
        bool result = false;

        context->sublevels_up++;
        result = query_tree_walker((Query*)node, (bool (*)())finalize_grouping_exprs_walker, (void*)context, 0);
        context->sublevels_up--;
        return result;
    }
    return expression_tree_walker(node, (bool (*)())finalize_grouping_exprs_walker, (void*)context);
}

/*
 * expand_groupingset_node -
 *      给定 GroupingSet 节点，展开它并返回一个列表的列表。
 *
 * 对于 EMPTY 节点，返回一个包含一个空列表的列表。
 *
 * 对于 SIMPLE 节点，返回一个包含一个列表的列表，该列表是节点的内容。
 *
 * 对于 CUBE 和 ROLLUP 节点，返回扩展的列表。
 *
 * 对于 SET 节点，递归展开包含的 CUBE 和 ROLLUP。
 */
static List* expand_groupingset_node(GroupingSet* gs)
{
    List* result = NIL;

    switch (gs->kind) {
        case GROUPING_SET_EMPTY:
            result = list_make1(NIL);
            break;

        case GROUPING_SET_SIMPLE:
            result = list_make1(gs->content);
            break;

        case GROUPING_SET_ROLLUP: {
            List* rollup_val = gs->content;
            ListCell* lc = NULL;
            int curgroup_size = list_length(gs->content);

            while (curgroup_size > 0) {
                List* current_result = NIL;
                int i = curgroup_size;

                foreach (lc, rollup_val) {
                    GroupingSet* gs_current = (GroupingSet*)lfirst(lc);

                    AssertEreport(gs_current->kind == GROUPING_SET_SIMPLE, MOD_OPT, "Kind is unexpected");

                    current_result = list_concat(current_result, list_copy(gs_current->content));

                    /* If we are done with making the current group, break */
                    if (--i == 0) {
                        break;
                    }
                }

                result = lappend(result, current_result);
                --curgroup_size;
            }

            result = lappend(result, NIL);
        } break;

        case GROUPING_SET_CUBE: {
            List* cube_list = gs->content;
            int number_bits = list_length(cube_list);
            uint32 num_sets;
            uint32 i;

            /* parser should cap this much lower */
            AssertEreport(number_bits < 31, MOD_OPT, "parser should cap this much lower");

            num_sets = (1U << (unsigned int)number_bits);

            for (i = 0; i < num_sets; i++) {
                List* current_result = NIL;
                ListCell* lc = NULL;
                uint32 mask = 1U;

                foreach (lc, cube_list) {
                    GroupingSet* gs_current = (GroupingSet*)lfirst(lc);

                    AssertEreport(gs_current->kind == GROUPING_SET_SIMPLE, MOD_OPT, "Kind is unexpected");

                    if (mask & i) {
                        current_result = list_concat(current_result, list_copy(gs_current->content));
                    }

                    mask <<= 1;
                }

                result = lappend(result, current_result);
            }
        } break;

        case GROUPING_SET_SETS: {
            ListCell* lc = NULL;

            foreach (lc, gs->content) {
                List* current_result = expand_groupingset_node((GroupingSet*)lfirst(lc));

                result = list_concat(result, current_result);
            }
        } break;
        default:
            break;
    }

    return result;
}

static int cmp_list_len_asc(const void* a, const void* b)
{
    int la = list_length(*(List* const*)a);
    int lb = list_length(*(List* const*)b);

    return (la > lb) ? 1 : (la == lb) ? 0 : -1;
}

/*
 * build_aggregate_fnexprs -
 *      为聚合构建转换和最终函数的表达式树。这些表达式树用于使聚合支持多态函数，因为这些函数在运行时可以使用 get_fn_expr_argtype() 发现实际的参数类型。
 *
 * agg_input_types、agg_state_type、agg_result_type 标识聚合的输入、转换和结果类型。这些应该都解析为实际类型（即不能是 ANYELEMENT 等）。
 * agg_input_collation 是聚合函数的输入排序规则。
 *
 * transfn_oid 和 finalfn_oid 标识要调用的函数；后者可能是 InvalidOid。
 *
 * 指向构造树的指针分别返回到 *transfnexpr 和 *finalfnexpr。如果没有 finalfn，则
 */
void build_aggregate_fnexprs(Oid* agg_input_types, int agg_num_inputs, Oid agg_state_type, Oid agg_result_type,
    Oid agg_input_collation, Oid transfn_oid, Oid finalfn_oid, Expr** transfnexpr, Expr** finalfnexpr)
{
    Param* argp = NULL;
    List* args = NIL;
    int i;

    /*
     * Build arg list to use in the transfn FuncExpr node. We really only care
     * that transfn can discover the actual argument types at runtime using
     * get_fn_expr_argtype(), so it's okay to use Param nodes that don't
     * correspond to any real Param.
     */
    argp = makeNode(Param);
    argp->paramkind = PARAM_EXEC;
    argp->paramid = -1;
    argp->paramtype = agg_state_type;
    argp->paramtypmod = -1;
    argp->paramcollid = agg_input_collation;
    argp->location = -1;

    args = list_make1(argp);

    for (i = 0; i < agg_num_inputs; i++) {
        argp = makeNode(Param);
        argp->paramkind = PARAM_EXEC;
        argp->paramid = -1;
        argp->paramtype = agg_input_types[i];
        argp->paramtypmod = -1;
        argp->paramcollid = agg_input_collation;
        argp->location = -1;
        args = lappend(args, argp);
    }

    *transfnexpr =
        (Expr*)makeFuncExpr(transfn_oid, agg_state_type, args, InvalidOid, agg_input_collation, COERCE_DONTCARE);

    /* see if we have a final function */
    if (!OidIsValid(finalfn_oid)) {
        *finalfnexpr = NULL;
        return;
    }

    /*
     * Build expr tree for final function
     */
    argp = makeNode(Param);
    argp->paramkind = PARAM_EXEC;
    argp->paramid = -1;
    argp->paramtype = agg_state_type;
    argp->paramtypmod = -1;
    argp->paramcollid = agg_input_collation;
    argp->location = -1;
    args = list_make1(argp);

    *finalfnexpr =
        (Expr*)makeFuncExpr(finalfn_oid, agg_result_type, args, InvalidOid, agg_input_collation, COERCE_DONTCARE);
}

/*
 * 为聚合函数的转换和最终函数创建表达式树。
 * 这些表达式树是必需的，以便在聚合函数中使用多态函数 --- 没有这些表达式树，
 * 这些函数将不知道它们应该使用的数据类型。
 * (实际上永远不会执行这些树，因此我们可以在正确性方面省点力气。)
 *
 * agg_input_types、agg_state_type、agg_result_type 分别标识聚合的输入、转换和结果的类型。
 * 这些类型应该解析为实际的类型（即，它们不应该是 ANYELEMENT 等）。
 * agg_input_collation 是聚合函数的输入排序规则。
 *
 * 对于有序集聚合，记住 agg_input_types 描述了直接参数，然后是聚合参数。
 *
 * transfn_oid 和 finalfn_oid 标识要调用的函数；后者可能是 InvalidOid。
 *
 * 指向构造树的指针存放在 *transfnexpr 和 *finalfnexpr 中。
 * 如果没有 finalfn，*finalfnexpr 将设置为 NULL。
 */
void build_trans_aggregate_fnexprs(int agg_num_inputs, int agg_num_direct_inputs, bool agg_ordered_set,
    bool agg_variadic, Oid agg_state_type, Oid* agg_input_types, Oid agg_result_type, Oid agg_input_collation,
    Oid transfn_oid, Oid finalfn_oid, Expr** transfnexpr, Expr** finalfnexpr)
{
    Param* argp = NULL;
    List* args = NULL;
    FuncExpr* fexpr = NULL;
    int i;

    /*
     * 构建用于 transfn FuncExpr 节点的参数列表。我们实际上只关心
     * transfn 能够在运行时使用 get_fn_expr_argtype() 发现实际的参数类型，
     * 所以可以使用不对应任何实际 Param 的 Param 节点。
     */
    argp = makeParam(PARAM_EXEC, -1, agg_state_type, -1, agg_input_collation, -1);
    args = list_make1(argp);

    for (i = agg_num_direct_inputs; i < agg_num_inputs; i++) {
        argp = makeParam(PARAM_EXEC, -1, agg_input_types[i], -1, agg_input_collation, -1);
        args = lappend(args, argp);
    }

    fexpr = makeFuncExpr(transfn_oid, agg_state_type, args, InvalidOid, agg_input_collation, COERCE_EXPLICIT_CALL);
    fexpr->funcvariadic = agg_variadic;
    *transfnexpr = (Expr*)fexpr;

    /* 检查是否有最终函数 */
    if (!OidIsValid(finalfn_oid)) {
        *finalfnexpr = NULL;
        return;
    }

    /*
     * 为最终函数构建表达式树
     */
    argp = makeParam(PARAM_EXEC, -1, agg_state_type, -1, agg_input_collation, -1);
    args = list_make1(argp);

    if (agg_ordered_set) {
        for (i = 0; i < agg_num_inputs; i++) {
            argp = makeParam(PARAM_EXEC, -1, agg_input_types[i], -1, agg_input_collation, -1);
            args = lappend(args, argp);
        }
    }

    *finalfnexpr =
        (Expr*)makeFuncExpr(finalfn_oid, agg_result_type, args, InvalidOid, agg_input_collation, COERCE_EXPLICIT_CALL);
    /* finalfn 当前从未被视为变长参数 */
}

/*
 * 为聚合函数的转换函数构建表达式树。
 */
void build_aggregate_transfn_expr(Oid *agg_input_types, int agg_num_inputs, int agg_num_direct_inputs,
                                  bool agg_variadic, Oid agg_state_type, Oid agg_input_collation, Oid transfn_oid,
                                  Expr **transfnexpr)
{
    Param *argp;
    List *args;
    FuncExpr *fexpr;
    int i;

    argp = makeNode(Param);
    argp->paramkind = PARAM_EXEC;
    argp->paramid = -1;
    argp->paramtype = agg_state_type;
    argp->paramtypmod = -1;
    argp->paramcollid = agg_input_collation;
    argp->location = -1;

    args = list_make1(argp);

    for (i = agg_num_direct_inputs; i < agg_num_inputs; i++) {
        argp = makeNode(Param);
        argp->paramkind = PARAM_EXEC;
        argp->paramid = -1;
        argp->paramtype = agg_input_types[i];
        argp->paramtypmod = -1;
        argp->paramcollid = agg_input_collation;
        argp->location = -1;
        args = lappend(args, argp);
    }

    fexpr = makeFuncExpr(transfn_oid, agg_state_type, args, InvalidOid, agg_input_collation, COERCE_EXPLICIT_CALL);
    fexpr->funcvariadic = agg_variadic;
    *transfnexpr = (Expr *)fexpr;
}

/*
 * 为聚合函数的最终函数构建表达式树。
 */
void build_aggregate_finalfn_expr(Oid *agg_input_types, int num_finalfn_inputs, Oid agg_state_type, Oid agg_result_type,
                                  Oid agg_input_collation, Oid finalfn_oid, Expr **finalfnexpr)
{
    Param *argp;
    List *args;
    int i;

    argp = makeNode(Param);
    argp->paramkind = PARAM_EXEC;
    argp->paramid = -1;
    argp->paramtype = agg_state_type;
    argp->paramtypmod = -1;
    argp->paramcollid = agg_input_collation;
    argp->location = -1;
    args = list_make1(argp);

    for (i = 0; i < num_finalfn_inputs - 1; i++) {
        argp = makeNode(Param);
        argp->paramkind = PARAM_EXEC;
        argp->paramid = -1;
        argp->paramtype = agg_input_types[i];
        argp->paramtypmod = -1;
        argp->paramcollid = agg_input_collation;
        argp->location = -1;
        args = lappend(args, argp);
    }

    *finalfnexpr =
        (Expr *)makeFuncExpr(finalfn_oid, agg_result_type, args, InvalidOid, agg_input_collation, COERCE_EXPLICIT_CALL);
}

/*
 * 将 groupingSets 子句展开为一个扁平的分组集合列表。
 * 返回的列表按长度排序，最短的集合排在前面。
 *
 * 主要用于规划器，但我们在这里也使用它来进行一些一致性检查。
 */
List* expand_grouping_sets(List* groupingSets, int limit)
{
    List* expanded_groups = NIL;
    List* result = NIL;
    double numsets = 1;
    ListCell* lc = NULL;

    if (groupingSets == NIL) {
        return NIL;
    }

    foreach (lc, groupingSets) {
        List* current_result = NIL;
        GroupingSet* gs = (GroupingSet*)lfirst(lc);
        current_result = expand_groupingset_node(gs);
        AssertEreport(current_result != NIL, MOD_OPT, "此处参数不应为 NULL");
        numsets *= list_length(current_result);

        if (limit >= 0 && numsets > limit) {
            return NIL;
        }

        expanded_groups = lappend(expanded_groups, current_result);
    }

    /*
     * 在 expanded_groups 的子列表之间执行笛卡尔积。在此过程中，
     * 从各个分组集合中删除任何重复的元素（但不能改变集合的数量）。
     */
    foreach (lc, (List*)linitial(expanded_groups)) {
        result = lappend(result, list_union_int(NIL, (List*)lfirst(lc)));
    }

    for_each_cell(lc, lnext(list_head(expanded_groups)))
    {
        List* p = (List*)lfirst(lc);
        List* new_result = NIL;
        ListCell* lc2 = NULL;

        foreach (lc2, result) {
            List* q = (List*)lfirst(lc2);
            ListCell* lc3 = NULL;

            foreach (lc3, p) {
                new_result = lappend(new_result, list_union_int(q, (List*)lfirst(lc3)));
            }
        }
        result = new_result;
    }

    if (list_length(result) > 1) {
        int result_len = list_length(result);
        List** buf = (List**)palloc(sizeof(List*) * result_len);
        List** ptr = buf;

        foreach (lc, result) {
            *ptr++ = (List*)lfirst(lc);
        }

        qsort(buf, result_len, sizeof(List*), cmp_list_len_asc);

        result = NIL;
        ptr = buf;

        while (result_len-- > 0)
            result = lappend(result, *ptr++);

        pfree_ext(buf);
    }

    return result;
}

/*
 * transformGroupingFunc
 *		转换 GROUPING 表达式
 *
 * GROUPING() 的行为与聚合函数非常相似。处理级别和嵌套的方式与聚合函数相同。
 * 我们也为这些表达式设置 p_hasAggs。
 */
Node* transformGroupingFunc(ParseState* pstate, GroupingFunc* p)
{
    ListCell* lc = NULL;
    List* args = p->args;
    List* result_list = NIL;
    bool orig_is_replace = false;

    GroupingFunc* result = makeNode(GroupingFunc);

    if (list_length(args) > 31) {
        ereport(ERROR,
            (errcode(ERRCODE_TOO_MANY_ARGUMENTS),
                errmsg("GROUPING 参数数量不能超过 32"),
                parser_errposition(pstate, p->location)));
    }
    orig_is_replace = pstate->isAliasReplace;

    /* Grouping 不支持别名替换。 */
    pstate->isAliasReplace = false;

    foreach (lc, args) {
        Node* current_result = NULL;
        current_result = transformExpr(pstate, (Node*)lfirst(lc), pstate->p_expr_kind);
        /* 表达式的可接受性稍后检查 */
        result_list = lappend(result_list, current_result);
    }

    pstate->isAliasReplace = orig_is_replace;

    result->args = result_list;
    result->location = p->location;

    if (pstate->p_is_flt_frame) {
        check_agglevels_and_constraints(pstate, (Node*)result);
    }

    pstate->p_hasAggs = true;

    return (Node*)result;
}

/*
 * check_windowagg_can_shuffle
 *		检查 windowagg 是否可以洗牌
 */
bool check_windowagg_can_shuffle(List* partitionClause, List* targetList)
{
    if (partitionClause == NIL) {
        return true;
    }

    ListCell* l = NULL;
    foreach (l, partitionClause) {
        SortGroupClause* grpcl = (SortGroupClause*)lfirst(l);
        TargetEntry* expr = get_sortgroupclause_tle(grpcl, targetList, false);
        if (expr == NULL) {
            continue;
        }
        if (checkExprHasAggs((Node*)expr->expr)) {
            return false;
        }
    }

    return true;
}

/*
 * get_aggregate_argtypes
 * 获取聚合调用传递的实际数据类型，并返回实际参数的数量。
 *
 * 给定一个 Aggref，提取输入参数的实际数据类型。
 * 对于有序集聚合（ordered-set agg），Aggref 包含直接参数和聚合参数，
 * 并且直接参数保存在聚合参数之前。
 *
 * 数据类型加载到 inputTypes[]，它必须引用长度为 FUNC_MAX_ARGS 的数组。
 */
int get_aggregate_argtypes(Aggref* aggref, Oid* inputTypes, int func_max_args)
{
    int narg = 0;
    ListCell* lc = NULL;

    /*
     * 如果是有序集聚合，aggref->aggdirectargs 不为 null。
     * 因此，我们需要首先处理直接参数。
     */
    foreach (lc, aggref->aggdirectargs) {
        inputTypes[narg] = exprType((Node*)lfirst(lc));
        narg++;
        if (narg >= func_max_args) {
            ereport(ERROR,
                (errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
                    errmsg("函数最多可以有 %d 个参数", func_max_args)));
        }
    }

    /*
     * 然后获取聚合参数，包括常规聚合和有序集聚合。
     */
    foreach (lc, aggref->args) {
        TargetEntry* tle = (TargetEntry*)lfirst(lc);

        /* 忽略普通聚合的排序列 */
        if (tle->resjunk) {
            continue;
        }

        inputTypes[narg] = exprType((Node*)tle->expr);
        narg++;
        if (narg >= func_max_args) {
            ereport(ERROR,
                (errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
                    errmsg("函数最多可以有 %d 个参数", func_max_args)));
        }
    }

    return narg;
}

/*
 * resolve_aggregate_transtype
 * 在聚合调用时，当 agg 接受 ANY 或多态类型时，确定过渡状态值的数据类型。
 *
 * 此函数解析多态聚合的状态数据类型。
 * 从 pg_aggregate 目录中传递 aggtranstype，以及通过 get_aggregate_argtypes 提取的实际参数类型。
 */
Oid resolve_aggregate_transtype(Oid aggfuncid, Oid aggtranstype, Oid* inputTypes, int numArguments)
{
    /* 仅在过渡状态为多态时解析实际类型 */
    if (IsPolymorphicType(aggtranstype)) {
        Oid* declaredArgTypes = NULL;
        int agg_nargs = 0;
        /* 获取 agg 函数的参数和结果类型... */
        (void)get_func_signature(aggfuncid, &declaredArgTypes, &agg_nargs);

        Assert(agg_nargs <= numArguments);

        aggtranstype = enforce_generic_type_consistency(inputTypes, declaredArgTypes, agg_nargs, aggtranstype, false);
        pfree(declaredArgTypes);
    }
    return aggtranstype;
}

#ifndef ENABLE_MULTIPLE_NODES
static void find_rownum_in_groupby_clauses(Rownum *rownumVar, check_ungrouped_columns_context *context)
{
    /*
     * have_non_var_grouping makes SQL
     * SELECT a + a FROM t GROUP BY a + a having rownum <= 1;
     * allowed, but SQL
     * SELECT a FROM t GROUP BY a having rownum <= 1;
     * not allowed, which is different from O.
     */
    if (!context->have_non_var_grouping) {
        bool haveRownum = false;
        ListCell *gl = NULL;
        foreach (gl, context->groupClauses) {
            Node *gnode = (Node *)((TargetEntry *)lfirst(gl))->expr;
            if (IsA(gnode, Rownum)) {
                haveRownum = true;
                break;
            }
        }

        if (haveRownum == false) {
            ereport(ERROR, (errcode(ERRCODE_GROUPING_ERROR),
                errmsg("ROWNUM 必须出现在 GROUP BY 子句中或在聚合函数中使用"),
                parser_errposition(context->pstate, rownumVar->location)));
        }
    }
}
#endif


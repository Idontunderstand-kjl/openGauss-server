/* -------------------------------------------------------------------------
 *
 * parse_startwith.cpp
 *    Implement start with related modules in transform state
 *
 * Portions Copyright (c) 1996-2021, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 * Portions Copyright (c) 2021, openGauss Contributors
 *
 *
 * IDENTIFICATION
 *    src/common/backend/parser/parse_startwith.cpp
 *
 * -------------------------------------------------------------------------
 */

#include "postgres.h"
#include "knl/knl_variable.h"

#include "miscadmin.h"

#include "access/heapam.h"
#include "catalog/catalog.h"
#include "catalog/heap.h"
#include "catalog/pg_synonym.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "commands/tablecmds.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/tlist.h"
#include "optimizer/planner.h"
#include "parser/analyze.h"
#include "parser/parsetree.h"
#include "parser/parse_clause.h"
#include "parser/parse_coerce.h"
#include "parser/parse_collate.h"
#include "parser/parse_expr.h"
#include "parser/parse_oper.h"
#include "parser/parse_relation.h"
#include "parser/parse_target.h"
#include "parser/parse_cte.h"
#include "pgxc/pgxc.h"
#include "rewrite/rewriteManip.h"
#include "storage/tcap.h"
#include "utils/guc.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "utils/rel_gs.h"
#include "utils/syscache.h"

/*
 ****************************************************************************************
 * @Brief: 兼容Oracle的START WITH...CONNECT BY支持，定义起始结构和相关例程
 *
 * @Note: 解析器中START WITH的唯一入口是transformStartWith()，其中所有内部实现都被隐藏在后面
 *
 ****************************************************************************************
 */

typedef struct StartWithTransformContext {
    ParseState* pstate;
    List *relInfoList;              // 关系信息列表
    List *where_infos;              // WHERE子句信息列表
    List *connectby_prior_name;     // CONNECT BY中的PRIOR列名列表
    Node *startWithExpr;            // START WITH子句表达式
    Node *connectByExpr;            // CONNECT BY子句表达式
    Node *whereClause;              // WHERE子句
    List *siblingsOrderBy;          // 兄弟节点的ORDER BY信息
    List *rownum_or_level_list;     // 行号或层级信息列表
    List *normal_list;              // 普通列表
    bool is_where;                  // 是否存在WHERE子句
    StartWithConnectByType connect_by_type;  // 连接类型

    /*
     * 用于多次推送的情况
     */
    List *fromClause;

    /*
     * connectByLevelExpr & connectByOtherExpr
     *
     * 通常为了性能考虑，对于level/rownum的连接，我们从connectByExpr中提取level/rownum表达式
     * - connectByOtherExpr：在RecursiveUnion的内部连接条件中评估
     * - connectByLevelExpr：在StartWithOp的节点中评估
     *
     * 例如：
     * connectByExpr: (level < 10) AND (t1.c1 > 1) AND (t1.c2 > 0)
     * connectByLevelExpr: level < 10
     * connectByOtherExpr: t1.c1 = 1 AND
     */
    Node *connectByLevelExpr;
    Node *connectByOtherExpr;
    bool nocycle;
} StartWithTransformContext;

typedef enum StartWithRewrite {
    SW_NONE = 0,
    SW_SINGLE,
    SW_FROMLIST,
    SW_JOINEXP,
} StaretWithRewrite;

typedef struct StartWithCTEPseudoReturnAtts {
    char    *colname;
    Oid      coltype;
    int32    coltypmod;
    Oid      colcollation;
} StartWithCTEPseudoReturnAtts;

// 定义伪返回列的信息
static StartWithCTEPseudoReturnAtts g_StartWithCTEPseudoReturnAtts[] =
{
    {"level", INT4OID, -1, InvalidOid},
    {"connect_by_isleaf", INT4OID, -1, InvalidOid},
    {"connect_by_iscycle", INT4OID, -1, InvalidOid},
    {"rownum", INT4OID, -1, InvalidOid}
};

// 解析START WITH子句和CONNECT BY子句的函数
static void transformStartWithClause(StartWithTransformContext *context, SelectStmt *stmt);

// 展开所有目标列表的函数
static List *expandAllTargetList(List *targetRelInfoList);

// 提取ColumnRef的辅助函数
static List *ExtractColumnRefStartInfo(ParseState *pstate, ColumnRef *column, char *relname, char *colname, Node *preResult);

// 处理SWCBColumnRef的辅助函数
static void HandleSWCBColumnRef(StartWithTransformContext* context, Node *node);

// StartWithWalker的辅助函数
static void StartWithWalker(StartWithTransformContext *context, Node *expr);

// 将WITH子句添加到分支的辅助函数
static void AddWithClauseToBranch(ParseState *pstate, SelectStmt *stmt, List *relInfoList);

// 转换单个RTE的辅助函数
static void transformSingleRTE(ParseState* pstate, Query* qry, StartWithTransformContext *context, Node *start_clause);

// 转换FROM列表的辅助函数
static void transformFromList(ParseState* pstate, Query* qry, StartWithTransformContext *context, Node *n);

// 转换START WITH CTE的辅助函数
static RangeTblEntry *transformStartWithCTE(ParseState* pstate, List *prior_names);

// 在解析PL/SQL参数之前跳过的辅助函数
static bool preSkipPLSQLParams(ParseState *pstate, ColumnRef *cref);

// 创建START WITH CTE的外部分支的辅助函数
static SelectStmt *CreateStartWithCTEOuterBranch(ParseState* pstate, StartWithTransformContext *context, List *relInfoList, Node *startWithExpr, Node *whereClause);

// 创建START WITH CTE的内部分支的辅助函数
static SelectStmt *CreateStartWithCTEInnerBranch(ParseState* pstate, StartWithTransformContext *context, List *relInfoList, Node *connectByExpr, Node *whereClause);

// 创建START WITH CTE的函数
static void CreateStartWithCTE(ParseState *pstate, Query *qry, SelectStmt *initpart, SelectStmt *workpart, StartWithTransformContext *context);

// 创建布尔A_CONST的函数
static Node *makeBoolAConst(bool state, int location);

// 选择SWCB策略的辅助函数
static StartWithRewrite ChooseSWCBStrategy(StartWithTransformContext context);

// 尝试替换虚假值的辅助函数
static Node *tryReplaceFakeValue(Node *node);

/*
 * ---------------------------------------------------------------------------------------
 *
 * Oracle兼容的"START WITH...CONNECT BY"支持例程
 *
 * ---------------------------------------------------------------------------------------
 */
/*
 ****************************************************************************************
 *  transformStartWith -
 *
 *  @Brief: Start With的主要入口点，所有内部实现都被隐藏在后面，
 *          处理实现如下：
 *
 *  exec_simple_query()
 *          -> parse_and_analyze()
 *                  -> transformStmt()
 *                          -> transformSelectStmt() {...详细信息如下...}
 *
 *  transformSelectStmt(pstate) {
 *      ...
 *      transformFromClause() {
 *          // 识别START WITH...CONNECT BY的目标关系，并创建相关的
 *          // StartWithTargetRelInfo，将它们放入parse->p_start_info中，
 *          // 稍后在顶层transformStartWith()中进行处理
 *      }
 *      ...
 *      transformStartWith() {
 *          // 1. 解析startWithExpr/connectByExpr
 *          transformStartWithClause();
 *
 *          // 2. 将START WITH...CONNECT BY对象转换为递归CTE
 *          transformSingleRTE() {
 *              // 2.1 构建CTE的左子树，即非递归项
 *              CreateStartWithCTEOuterBranch();
 *
 *              // 2.2 构建CTE的右子树，即递归项
 *              CreateStartWithCTEInnerBranch();
 *
 *              // 2.3 构建start with转换后的CTE对象
 *              CreateStartWithCTE();
 *
 *              // 2.4 像常规的with-recursive一样正常转换start with CTE
 *              transformStartWithCTE();
 *          }
 *      }
 *   }
 *
 ****************************************************************************************
 */
void transformStartWith(ParseState *pstate, SelectStmt *stmt, Query *qry)
{
    ListCell *lc = NULL;
    StartWithTransformContext context;

    if (pstate->p_start_info == NULL) {
        ereport(ERROR,
               (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
               errmsg("在fromclause中找不到可以由start with/connect by重写的正确元素。"),
               errdetail("仅支持在fromclause中的表和子查询可以被重写。")));
    }

    errno_t rc = memset_s(&context, sizeof(StartWithTransformContext),
                0, sizeof(StartWithTransformContext));
    securec_check(rc, "\0", "\0");

    context.pstate = pstate;
    context.relInfoList = NULL;
    context.connectby_prior_name = NULL;

    transformStartWithClause(&context, stmt);
    pstate->p_hasStartWith = true;

    int lens = list_length(pstate->p_start_info);
    if (lens != 1) {
        context.relInfoList = pstate->p_start_info;
        context.fromClause = pstate->sw_fromClause;
    }

    /* 将结果RTE设置为已替换标志 */
    foreach(lc, context.relInfoList) {
        StartWithTargetRelInfo *info = (StartWithTargetRelInfo *)lfirst(lc);
        info->rte->swAborted = true;
    }

    /* 选择SWCB重写策略。 */
    StartWithRewrite op = ChooseSWCBStrategy(context);
    if (op == SW_SINGLE) {
        transformSingleRTE(pstate, qry, &context, (Node *)stmt->startWithClause);
    } else {
        transformFromList(pstate, qry, &context, (Node *)stmt->startWithClause);
    }

    return;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: transform阶段的SWCB的辅助函数，在这里我们为每个应用了"start with"的FromClauseItem创建StartWithInfo对象，
 *         并将其插入到pstate中，通常我们处理以下情况：
 *              - RangeVar(baserel)
 *              - RangeSubSelect (子查询)
 *              - 未来将考虑函数和CTE
 *
 * @Param
 *    - pstate: 解析阶段
 *    - n: 一个FromClauseItem
 *    - rte: 相关的FromClauseItem RTE
 *    - rte: 相关的FromClauseItem RTR
 *
 * @Return: 无
 * --------------------------------------------------------------------------------------
 */
void AddStartWithTargetRelInfo(ParseState* pstate, Node* relNode,
                RangeTblEntry* rte, RangeTblRef *rtr)
{
    StartWithTargetRelInfo *startInfo = makeNode(StartWithTargetRelInfo);

    if (IsA(relNode, RangeVar)) {
        RangeVar* rv = (RangeVar*)relNode;

        startInfo->relname = rv->relname;
        if (rv->alias != NULL) {
            startInfo->aliasname = rv->alias->aliasname;
        }
        startInfo->rte = rte;
        startInfo->rtr = rtr;
        startInfo->rtekind = rte->rtekind;

        RangeVar *tbl = (RangeVar *)copyObject(relNode);

        startInfo->tblstmt = (Node *)tbl;
        startInfo->columns = rte->eref->colnames;
    } else if (IsA(relNode, RangeSubselect)) {
        RangeSubselect *sub = (RangeSubselect *)relNode;

        /* 名称为 __unnamed_subquery__ */
        if (pg_strcasecmp(sub->alias->aliasname, "__unnamed_subquery__") != 0) {
            startInfo->aliasname = sub->alias->aliasname;
        } else {
            char swname[NAMEDATALEN];
            int rc = snprintf_s(swname, sizeof(swname), sizeof(swname) - 1,
                                "sw_subquery_%d", pstate->sw_subquery_idx);
            securec_check_ss(rc, "", "");
            pstate->sw_subquery_idx++;

            sub->alias->aliasname = pstrdup(swname);
            startInfo->aliasname = sub->alias->aliasname;
        }

        SelectStmt *substmt = (SelectStmt *)sub->subquery;
        if (substmt->withClause == NULL) {
            substmt->withClause = (WithClause *)copyObject(pstate->origin_with);
        }
        startInfo->rte = rte;
        startInfo->rtr = rtr;
        startInfo->rtekind = rte->rtekind;
        startInfo->tblstmt = relNode;
        startInfo->columns = rte->eref->colnames;
    } else {
        ereport(ERROR,
                (errcode(ERRCODE_UNRECOGNIZED_NODE_TYPE),
                errmsg("不支持不识别的节点类型: %d %s 在AddStartWithInfo中。",
                (int)nodeTag(relNode), nodeToString(relNode))));
    }

    pstate->p_start_info = lappend(pstate->p_start_info, startInfo);

    return;
}
/*
 * --------------------------------------------------------------------------------------
 * @Brief: 为转换后的RTE生成虚拟目标名称，将关系重命名为 "t1" -> "tmp_result", "t1.c1" -> "tmp_result@c1"
 *
 * @param:
 *      - alias: 基础CTE的ctename
 *      - colname: 基础表的属性名
 *
 * @Return: 虚拟列名的复制字符串版本
 * --------------------------------------------------------------------------------------
 */
char *makeStartWithDummayColname(char *alias, char *column)
{
    errno_t rc;
    char *result = NULL;
    char *split = "@";
    char dumy_name[NAMEDATALEN];

    int total = strlen(alias) + strlen(column) + strlen(split);
    if (total >= NAMEDATALEN) {
        ereport(ERROR,
                (errcode(ERRCODE_UNRECOGNIZED_NODE_TYPE),
                errmsg("Exceed maximum StartWithDummayColname length %d, relname %s, column %s.",
                total, alias, column)));
    }

    rc = memset_s(dumy_name, NAMEDATALEN, 0, NAMEDATALEN);
    securec_check_c(rc, "\0", "\0");
    rc = strncat_s(dumy_name, NAMEDATALEN, alias, strlen(alias));
    securec_check_c(rc, "\0", "\0");

    /* 添加分隔符 @ */
    rc = strncat_s(dumy_name, NAMEDATALEN, split, strlen(split));
    securec_check_c(rc, "\0", "\0");

    rc = strncat_s(dumy_name, NAMEDATALEN, column, strlen(column));
    securec_check_c(rc, "\0", "\0");

    result = pstrdup(dumy_name);

    return result;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 适应性调整SELECT语句，用于转换后的RTE
 *
 * @param:
 *      - pstate: 解析状态
 *      - stmt: SELECT语句
 *
 * @Return: 无
 * --------------------------------------------------------------------------------------
 */
void AdaptSWSelectStmt(ParseState *pstate, SelectStmt *stmt)
{
    ListCell *lc = NULL;
    List *tbls = NULL;

    foreach(lc, pstate->p_start_info) {
        StartWithTargetRelInfo *info = (StartWithTargetRelInfo *)lfirst(lc);

        if (!info->rte->swAborted) {
            tbls = lappend(tbls, info->tblstmt);
        }
    }

    RangeVar *cte = makeRangeVar(NULL, "tmp_reuslt", -1);
    tbls = lappend(tbls, cte);

    stmt->fromClause = tbls;

    return;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 判断RTE是否是经过SWCB重写的
 *
 * @param:
 *      - rte: RangeTblEntry
 *
 * @Return: 是否经过SWCB重写
 * --------------------------------------------------------------------------------------
 */
bool IsSWCBRewriteRTE(RangeTblEntry *rte)
{
    bool result = false;

    if (rte->rtekind != RTE_CTE) {
        return result;
    }

    if (pg_strcasecmp(rte->ctename, "tmp_reuslt") != 0) {
        return result;
    }

    result = rte->swConverted;
    return result;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 判断查询是否经过SWCB重写
 *
 * @param:
 *      - query: 查询
 *
 * @Return: 是否经过SWCB重写
 * --------------------------------------------------------------------------------------
 */
bool IsQuerySWCBRewrite(Query *query)
{
    bool isSWCBRewrite = false;
    ListCell *lc = NULL;

    foreach(lc, query->rtable) {
        RangeTblEntry *rte = (RangeTblEntry *)lfirst(lc);

        /*
         * 只有RTE_CTE才能被重写为startwith CTE，其他跳过。
         * */
        if (rte->rtekind != RTE_CTE) {
            continue;
        }

        if (pg_strcasecmp(rte->ctename, "tmp_reuslt") == 0) {
            isSWCBRewrite = true;
            break;
        }
    }

    return isSWCBRewrite;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 选择 START WITH...CONNECT BY 重写策略
 *
 * @param:
 *      - context: StartWithTransformContext 上下文
 *
 * @Return: 重写策略
 * --------------------------------------------------------------------------------------
 */
static StartWithRewrite ChooseSWCBStrategy(StartWithTransformContext context)
{
    StartWithRewrite op = SW_NONE;
    int info_lens = list_length(context.relInfoList);

    /*
     * 只有一个 StartWithInfos 时使用 SW_SINGLE 策略，多个则使用 SW_FROMLIST 策略。其他情况待处理。
     */
    if (info_lens == 1) {
        op = SW_SINGLE;
    } else {
        op = SW_FROMLIST;
    }

    return op;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 在 transform 阶段预检查 PLSQL 输入/输出列是否与 transformColumnRef 相同
 *
 * @param: pstate 解析状态
 *
 * @Return: 在 startWithWalker 过程中是否跳过这些列
 * --------------------------------------------------------------------------------------
 */
static bool preSkipPLSQLParams(ParseState *pstate, ColumnRef *cref)
{
    Node* node = NULL;

    /*
     * 给予 PreParseColumnRefHook，如果有的话，首先尝试调用它。
     * 如果返回非空，则结束。
     */
    if (pstate->p_pre_columnref_hook != NULL) {
        node = (*pstate->p_pre_columnref_hook)(pstate, cref);
        if (node != NULL) {
            return true;
        }
    }

    if (pstate->p_post_columnref_hook != NULL) {
        Node* hookresult = NULL;

        /*
         * 如果 node 不是表列，我们应该将一个空值传递给 hook，否则它会将 columnref 误判为不明确。
         */
        hookresult = (*pstate->p_post_columnref_hook)(pstate, cref, node);
        if (hookresult != NULL) {
            return true;
        }
    }

    return false;
}

/**
 * @param preResult Var 结构
 * @return 如果是上层查询的列则返回 true
 */
static inline bool IsAUpperQueryColumn(Node *preResult)
{
    if (IsA(preResult, Var)) {
        Var *varNode = (Var *)preResult;
        if (!IS_SPECIAL_VARNO(varNode->varno) && varNode->varlevelsup >= 1) {
            return true;
        }
    }
    return false;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 待添加
 *
 * @param: 待添加
 *
 * @Return: 待添加
 * --------------------------------------------------------------------------------------
 */
static List *ExtractColumnRefStartInfo(ParseState *pstate, ColumnRef *column, char *relname, char *colname,
                                       Node *preResult)
{
    ListCell *lc1 = NULL;
    ListCell *lc2 = NULL;
    List *extract_infos = NIL;

    foreach(lc1, pstate->p_start_info) {
        StartWithTargetRelInfo *start_info = (StartWithTargetRelInfo *)lfirst(lc1);

        bool column_exist = false;
        /*
         * 如果 relname 不存在，则检查列名；
         * 否则直接检查 StartWithInfo 的 relname/aliasname。
         */
        if (relname == NULL) {
            foreach(lc2, start_info->columns) {
                Value *val = (Value *)lfirst(lc2);
                if (strcmp(colname, strVal(val)) == 0) {
                    column_exist = true;
                    break;
                }
            }
        } else {
            if (start_info->aliasname != NULL &&
                        strcmp(start_info->aliasname, relname) == 0) {
                column_exist = true;
            } else if (start_info->relname != NULL &&
                        strcmp(start_info->relname, relname) == 0) {
                column_exist = true;
            } else {
                column_exist = false;
            }
        }

        /* 处理子 StartWith CTE 的目标列表 */
        if (start_info->rte->swSubExist) {
            Assert(start_info->rtekind == RTE_SUBQUERY);

            foreach(lc2, start_info->columns) {
                Value *val = (Value *)lfirst(lc2);
                if (strstr(strVal(val), colname)) {
                    column_exist = true;
                    colname = pstrdup(strVal(val));
                    break;
                }
            }
        }

        if (column_exist) {
            extract_infos = lappend(extract_infos, start_info);

            if (start_info->rtekind == RTE_RELATION) {
                relname = start_info->aliasname ? start_info->aliasname : start_info->relname;
            } else if (start_info->rtekind == RTE_SUBQUERY) {
                relname = start_info->aliasname;
            } else if (start_info->rtekind == RTE_CTE) {
                relname = start_info->aliasname ? start_info->aliasname : start_info->relname;
            }

            column->fields = list_make2(makeString(relname), makeString(colname));
        }
    }

    if (list_length(extract_infos) > 1) {
        ereport(ERROR,
               (errcode(ERRCODE_AMBIGUOUS_COLUMN),
                errmsg("column reference \"%s\" is ambiguous.", colname)));
    }

    if (list_length(extract_infos) == 0 && !IsAUpperQueryColumn(preResult)) {
        ereport(WARNING,
               (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
               errmsg("Cannot match table with startwith/connectby column %s.%s, maybe it is an upper query column",
                      relname, colname)));
    }

    return extract_infos;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 在startWithWalker()中调用的辅助函数，用于转换ConnectBy或StartWith表达式，
 *         当遇到ColumnRef节点时，需要通过调用makeStartWithDummayColname()将其评估为
 *         "baserel->cte"格式
 *
 * @param:
 *     - context: startwith转换上下文
 *     - node: ColumnRef节点，基本上我们需要假设它是ColumnRef类型
 *
 * @Return: 无
 * --------------------------------------------------------------------------------------
 */
static void HandleSWCBColumnRef(StartWithTransformContext *context, Node *node)
{
    List *result = NIL;
    char *relname = NULL;
    char *colname = NULL;
    ParseState *pstate = context->pstate;

    if (node == NULL) {
        return;
    }

    Assert(nodeTag(node) == T_ColumnRef);
    ColumnRef *column = (ColumnRef *)node;
    bool prior = column->prior;
    char *initname = strVal(linitial(column->fields));

    if (pg_strcasecmp(initname, "tmp_reuslt") == 0) {
        return;
    }

    /* 在过程中跳过参数 */
    if (preSkipPLSQLParams(pstate, column) && !prior) {
        return;
    }

    ColumnRef *preColumn = (ColumnRef *)copyObject(column);
    Node *preResult = transformColumnRef(pstate, preColumn);
    if (preResult == NULL) {
        return;
    }

    int len = list_length(column->fields);
    switch (len) {
        case 1: {
            Node *field1 = (Node *)linitial(column->fields);
            colname = strVal(field1);

            /*
             * 在原地将columnref替换为两个字段，例如将id转换为test.id，
             * 这对于之后的SWCB重写非常有帮助。因此，在ExtractColumnRefStartInfo之后，
             * 此处的columnref将包含两个字段。
             */
            result = ExtractColumnRefStartInfo(pstate, column, NULL, colname, preResult);

            if (!prior) {
                break;
            }

            if (list_length(column->fields) <= 1) {
                ereport(ERROR,
                    (errmodule(MOD_PARSER), errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("在START WITH / CONNECT BY子句中存在无效的列引用。"),
                        errdetail("引用的列可能不存在。"),
                        errcause("通常在引用的列不存在时发生这种情况。"),
                        erraction("请检查并修订您的查询或联系华为工程师。")));
            }

            char *dummy = makeStartWithDummayColname(
                strVal(linitial(column->fields)),
                strVal(lsecond(column->fields)));

            column->fields = list_make2(makeString("tmp_reuslt"), makeString(dummy));

            /* 记录工作表名 */
            context->connectby_prior_name = lappend(context->connectby_prior_name,
                                                     makeString(dummy));

            break;
        }
        case 2: {
            Node *field1 = (Node *)linitial(column->fields);
            Node *field2 = (Node *)lsecond(column->fields);
            relname = strVal(field1);
            colname = strVal(field2);

            result = ExtractColumnRefStartInfo(pstate, column, relname, colname, preResult);

            if (prior) {
                char *dummy = makeStartWithDummayColname(
                    strVal(linitial(column->fields)),
                    strVal(lsecond(column->fields)));
                column->fields = list_make2(makeString("tmp_reuslt"), makeString(dummy));

                /* 记录工作表名 */
                context->connectby_prior_name = lappend(context->connectby_prior_name,
                                                         makeString(dummy));
            }

            break;
        }
        default: {
            ereport(ERROR,
                    (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                     errmsg("在HandleSWCBColumnRef中不支持 %d 列长度", len)));
        }
    }

    if (context->is_where) {
        context->where_infos = list_concat_unique(context->where_infos, result);
    } else {
        context->relInfoList = list_concat_unique(context->relInfoList, result);
    }

    return;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 根据列名判断表达式是否为ColumnRef
 *
 * @param:
 *      - expr: 表达式节点
 *      - col_name: 列名
 *
 * @Return: 如果是ColumnRef并且列名匹配，返回true，否则返回false
 * --------------------------------------------------------------------------------------
 */
static bool is_cref_by_name(Node *expr, const char *col_name)
{
    if (expr == NULL || !IsA(expr, ColumnRef)) {
        return false;
    }
    ColumnRef *cref = (ColumnRef *)expr;
    char *colname = NameListToString(cref->fields);
    bool ret = (strcasecmp(colname, col_name) == 0) ? true : false;
    pfree(colname);
    return ret;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 创建整数常量节点
 *
 * @param:
 *      - val: 整数值
 *      - location: 位置信息
 *
 * @Return: 返回A_Const节点指针
 * --------------------------------------------------------------------------------------
 */
static Node *makeIntConst(int val, int location)
{
    A_Const *n = makeNode(A_Const);

    n->val.type = T_Integer;
    n->val.val.ival = val;
    n->location = location;

    return (Node *)n;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 替换List中的虚拟值
 *
 * @param:
 *      - lst: 待替换的List
 *
 * @Return: 如果替换成功，返回替换后的List，否则返回原始List
 * --------------------------------------------------------------------------------------
 */
static Node *replaceListFakeValue(List *lst)
{
    List *newArgs = NIL;
    ListCell *lc = NULL;
    bool replaced = false;

    /* 用虚拟常数替换level/rownum var属性 */
    foreach (lc, lst) {
        Node *n = (Node *)lfirst(lc);
        Node *newNode = tryReplaceFakeValue(n);
        if (newNode != n) {
            replaced = true;
            n = newNode;
        }
        newArgs = lappend(newArgs, n);
    }
    return replaced ? (Node *)newArgs : (Node *)lst;
}
/*
 * --------------------------------------------------------------------------------------
 * @Brief: 尝试替换节点中的假值
 * @Param:
 *     - node: 节点
 * @Return: 替换后的节点
 * --------------------------------------------------------------------------------------
 */
static Node *tryReplaceFakeValue(Node *node)
{
    if (node == NULL) {
        return node;
    }

    if (IsA(node, Rownum)) {
        node = makeIntConst(CONNECT_BY_ROWNUM_FAKEVALUE, -1);
    } else if (is_cref_by_name(node, "level")) {
        node = makeIntConst(CONNECT_BY_LEVEL_FAKEVALUE, -1);
    } else if (IsA(node, List)) {
        node = replaceListFakeValue((List *) node);
    }
    return node;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 伪行号/层次行号遍历器
 * @Param:
 *     - node: 节点
 *     - context_parent_node: 上下文父节点
 * @Return: 布尔值
 * --------------------------------------------------------------------------------------
 */
static bool pseudo_level_rownum_walker(Node *node, Node *context_parent_node)
{
    if (node == NULL) {
        return false;
    }

    Node* newNode = tryReplaceFakeValue(node);

    /* Case 1: 未发生假值替换。立即返回。 */
    if (newNode == node) {
        return raw_expression_tree_walker(node, (bool (*)()) pseudo_level_rownum_walker, node);
    }

    /* Case 2: 发生假值替换。需要更新父节点 */
    switch (nodeTag(context_parent_node)) {
        case T_A_Expr: {
            A_Expr *expr = (A_Expr *) context_parent_node;
            if (expr->lexpr == node) {
                expr->lexpr = newNode;
            } else {
                expr->rexpr = newNode;
            }
            break;
        }
        case T_TypeCast: {
            TypeCast *tc = (TypeCast *) context_parent_node;
            tc->arg = newNode;
            break;
        }
        case T_NullTest: {
            NullTest *nt = (NullTest *) context_parent_node;
            nt->arg = (Expr*) newNode;
            break;
        }
        case T_FuncCall: {
            FuncCall *fc = (FuncCall *) context_parent_node;
            fc->args = (List *)newNode;
            break;
        }
        default:
            break;
    }
    return raw_expression_tree_walker(node, (bool (*)()) pseudo_level_rownum_walker, node);
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 检查表达式中是否存在 rownum/level/prior，如果给定表达式同时包含 prior 和 rownum/level，
 *          则报错。
 * --------------------------------------------------------------------------------------
*/
static void rowNumOrLevelWalker(Node *expr, bool *hasRownumOrLevel, bool *hasPrior)
{
    if (expr == NULL || (*hasRownumOrLevel && *hasPrior)) {
        return;
    }

    switch (nodeTag(expr)) {
        case T_ColumnRef: {
            ColumnRef* colRef = (ColumnRef*)expr;
            *hasRownumOrLevel = is_cref_by_name((Node *)colRef, "level") || *hasRownumOrLevel;
            *hasPrior = colRef->prior || *hasPrior;
            break;
        }

        case T_Rownum: {
            *hasRownumOrLevel = true;
            break;
        }

        case T_NullTest: {
            NullTest* nullTestExpr = (NullTest*)expr;
            Node* arg = (Node *)nullTestExpr->arg;
            rowNumOrLevelWalker(arg, hasRownumOrLevel, hasPrior);
            break;
        }

        case T_SubLink: {
            SubLink *sublink = (SubLink *)expr;
            Node *testexpr = sublink->testexpr;
            rowNumOrLevelWalker(testexpr, hasRownumOrLevel, hasPrior);
            break;
        }

        case T_CoalesceExpr: {
            Node* node = (Node *)(((CoalesceExpr*)expr)->args);
            rowNumOrLevelWalker(node, hasRownumOrLevel, hasPrior);
            break;
        }

        case T_CollateClause: {
            CollateClause *cc = (CollateClause*) expr;
            rowNumOrLevelWalker(cc->arg, hasRownumOrLevel, hasPrior);
            break;
        }

        case T_TypeCast: {
            TypeCast* tc = (TypeCast*)expr;
            rowNumOrLevelWalker(tc->arg, hasRownumOrLevel, hasPrior);
            break;
        }

        case T_List: {
            List* l = (List*)expr;
            ListCell* lc = NULL;
            foreach (lc, l) {
                rowNumOrLevelWalker((Node*)lfirst(lc), hasRownumOrLevel, hasPrior);
            }
            break;
        }

        case T_FuncCall: {
            ListCell *args = NULL;
            FuncCall* fn = (FuncCall *)expr;

            foreach (args, fn->args) {
                rowNumOrLevelWalker((Node*)lfirst(args), hasRownumOrLevel, hasPrior);
            }
            break;
        }

        case T_A_Indirection: {
            A_Indirection* idn = (A_Indirection *)expr;
            rowNumOrLevelWalker(idn->arg, hasRownumOrLevel, hasPrior);
            break;
        }

        case T_A_Expr: {
            A_Expr *a_expr = (A_Expr *)expr;
            Node *left_expr = a_expr->lexpr;
            Node *right_expr = a_expr->rexpr;

            switch (a_expr->kind) {
                case AEXPR_OP:
                case AEXPR_AND:
                case AEXPR_OR:
                case AEXPR_IN: {
                    rowNumOrLevelWalker(left_expr, hasRownumOrLevel, hasPrior);
                    rowNumOrLevelWalker(right_expr, hasRownumOrLevel, hasPrior);
                    break;
                }
                case AEXPR_NOT: {
                    rowNumOrLevelWalker(right_expr, hasRownumOrLevel, hasPrior);
                    break;
                }
                default: {
                    ereport(ERROR,
                        (errmodule(MOD_PARSER), errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                            errmsg("在 START WITH / CONNECT BY 子句中发现不支持的表达式"
                                "在 rowNumOrLevelWalker 中。"),
                            errdetail("不支持的表达式类型: %d。", (int)a_expr->kind),
                            errcause("在 START WITH / CONNECT BY 子句中发现不支持的表达式。"),
                            erraction("请检查并修改查询，或联系华为工程师。")));
                    break;
                }
            }
            break;
        }
        case T_A_Const: {
            A_Const *n = (A_Const *)expr;
            if (n->val.type == T_Integer) {
                long val = n->val.val.ival;
                if (val == CONNECT_BY_ROWNUM_FAKEVALUE || val == CONNECT_BY_LEVEL_FAKEVALUE) {
                    *hasRownumOrLevel = true;
                }
            }
            break;
        }
        case T_A_ArrayExpr:
        case T_ParamRef: {
            break;
        }

        default: {
            ereport(ERROR,
                (errmodule(MOD_PARSER), errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                    errmsg("在 START WITH / CONNECT BY 子句中发现不支持的表达式"
                        "在 rowNumOrLevelWalker 中。"),
                    errdetail("不支持的节点类型: %d。", (int)nodeTag(expr)),
                    errcause("在 START WITH / CONNECT BY 子句中发现不支持的表达式。"),
                    erraction("请检查并修改查询，或联系华为工程师。")));
            break;
        }
    }

    return;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 将 connectByExpr 展开成两个列表
 * @Param:
 *      - rownum_or_level_list: 包含 "level" 或 "rownum" 表达式的列表
 *      - normal_list: 包含 "connectByExpr - rownum_or_level_list" 表达式的列表
 *      - expr: 表达式
 * --------------------------------------------------------------------------------------
*/
static void flattenConnectByExpr(StartWithTransformContext *context, Node *expr)
{
    if (expr == NULL) {
        return;
    }

    bool hasRownumOrLevel = false;
    bool hasPrior = false;
    if (nodeTag(expr) == T_A_Expr) {
        A_Expr *a_expr = (A_Expr *)expr;
        if (a_expr->kind ==  AEXPR_AND) {
            Node *lexpr = a_expr->lexpr;
            Node *rexpr = a_expr->rexpr;
            flattenConnectByExpr(context, lexpr);
            flattenConnectByExpr(context, rexpr);
            return;
        }
    }

    rowNumOrLevelWalker(expr, &hasRownumOrLevel, &hasPrior);
    if (hasRownumOrLevel && hasPrior) {
        ereport(ERROR, (errmodule(MOD_PARSER), errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
            errmsg("由 prior 指定的列不能与 ROWNUM/LEVEL 重合。"),
            errdetail("不支持的节点类型: %d.", (int)nodeTag(expr)),
            errcause("在 START WITH / CONNECT BY 子句中发现不支持的表达式。"),
            erraction("请检查并修改查询，或联系华为工程师。")));
    }
    if (hasRownumOrLevel) {
        context->rownum_or_level_list = lappend(context->rownum_or_level_list, expr);
    } else {
        context->normal_list = lappend(context->normal_list, expr);
    }
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief:  使用 "AND" 从给定的列表构建内部表达式
 * @Return: 最终的表达式
 * --------------------------------------------------------------------------------------
*/
static Node *buildExprUsingAnd(ListCell *tempCell)
{
    if (tempCell == NULL) {
        return NULL;
    }

    Node *nowExpr = (Node *)lfirst(tempCell);
    Node *nextExpr = buildExprUsingAnd(lnext(tempCell));

    if (nextExpr != NULL) {
        return (Node *)makeA_Expr(AEXPR_AND, NULL, nowExpr, nextExpr, -1);
    } else {
        return nowExpr;
    }
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: SWCB 的表达式处理函数，通常有两种处理方式
 *    (1). 递归查找基本列并对列名进行规范化，例如：
 *         c1 -> t1.c1，目的是为后续处理提供更多详细信息
 *    (2). 查找常量并标识 CONNECT BY 类型 ROWNUM/LEVEL
 *
 * @param
 *    - context: SWCB 表达式处理上下文，保存正在处理的状态和一些处理结果
 *    - expr: 表达式节点
 *
 * @return: 无，一些信息在 *context 下返回
 * --------------------------------------------------------------------------------------
 */
static void StartWithWalker(StartWithTransformContext *context, Node *expr)
{
    if (expr == NULL) {
        return;
    }

    check_stack_depth();

    switch (nodeTag(expr)) {
        case T_ColumnRef: {
            ColumnRef* colRef = (ColumnRef*)expr;
            HandleSWCBColumnRef(context, (Node *)colRef);
            break;
        }

        case T_NullTest: {
            NullTest* nullTestExpr = (NullTest*)expr;
            Node* arg = (Node *)nullTestExpr->arg;
            if (arg != NULL && nodeTag(arg) == T_ColumnRef) {
                HandleSWCBColumnRef(context, arg);
            } else {
                StartWithWalker(context, arg);
            }
            break;
        }

        case T_SubLink: {
            SubLink *sublink = (SubLink *)expr;
            Node *testexpr = sublink->testexpr;
            if (testexpr != NULL && nodeTag(testexpr) == T_ColumnRef) {
                HandleSWCBColumnRef(context, testexpr);
            } else {
                StartWithWalker(context, testexpr);
            }
            break;
        }

        case T_CoalesceExpr: {
            Node* node = (Node *)(((CoalesceExpr*)expr)->args);
            StartWithWalker(context, node);
            break;
        }

        case T_CollateClause: {
            CollateClause *cc = (CollateClause*) expr;
            StartWithWalker(context, cc->arg);
            break;
        }

        case T_TypeCast: {
            TypeCast* tc = (TypeCast*)expr;
            StartWithWalker(context, tc->arg);
            break;
        }

        case T_List: {
            List* l = (List*)expr;
            ListCell* lc = NULL;
            foreach (lc, l) {
                StartWithWalker(context, (Node*)lfirst(lc));
            }
            break;
        }

        case T_A_ArrayExpr: {
            break;
        }

        case T_FuncCall: {
            ListCell *args = NULL;
            FuncCall* fn = (FuncCall *)expr;

            foreach (args, fn->args) {
                StartWithWalker(context, (Node*)lfirst(args));
            }
            break;
        }

        case T_A_Indirection: {
            A_Indirection* idn = (A_Indirection *)expr;
            StartWithWalker(context, idn->arg);
            break;
        }

        case T_A_Expr: {
            A_Expr *a_expr = (A_Expr *)expr;

            switch (a_expr->kind) {
                case AEXPR_OP: {
                    Node *left_expr = a_expr->lexpr;
                    Node *right_expr = a_expr->rexpr;

                    if (left_expr != NULL && (is_cref_by_name(left_expr, "level") ||
                            IsA(left_expr, Rownum))) {
                        context->connect_by_type = CONNECT_BY_MIXED_LEVEL;
                        A_Const *n = makeNode(A_Const);
                        n->val.type = T_Integer;
                        n->val.val.ival = IsA(left_expr, Rownum) ?
                            CONNECT_BY_ROWNUM_FAKEVALUE : CONNECT_BY_LEVEL_FAKEVALUE;
                        n->location = -1;
                        a_expr->lexpr = (Node*) n;
                        break;
                    }

                    /* 转换 AEXPR_OP 周围的 right/left 表达式 */
                    if (left_expr != NULL && nodeTag(left_expr) == T_ColumnRef) {
                        HandleSWCBColumnRef(context, left_expr);
                    } else {
                        StartWithWalker(context, left_expr);
                    }

                    if (right_expr != NULL && nodeTag(right_expr) == T_ColumnRef) {
                        HandleSWCBColumnRef(context, right_expr);
                    } else {
                        StartWithWalker(context, right_expr); 
                    }

                    break;
                }
                case AEXPR_AND:
                case AEXPR_OR: {
                    /* 在进入 lexpr 之前深拷贝 rexpr：
                       这是为了防止 lexpr 转换过程中修改 rexpr，
                       在 lexpr 和 rexpr 共享公共节点的情况下，比如 'between ... and ...' 子句
                       中，在 lexpr 和 rexpr 中找到了重复的列引用 */
                    a_expr->rexpr = (Node*) copyObject(a_expr->rexpr);
                    StartWithWalker(context, a_expr->lexpr);
                    StartWithWalker(context, a_expr->rexpr);
                    break;
                }
                case AEXPR_IN: {
                    StartWithWalker(context, a_expr->lexpr);
                    StartWithWalker(context, a_expr->rexpr);
                    break;
                }
                case AEXPR_NOT: {
                    StartWithWalker(context, a_expr->rexpr);
                    break;
                }
                default: {
                    ereport(ERROR,
                        (errmodule(MOD_PARSER), errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                            errmsg("在 START WITH / CONNECT BY 子句中发现不支持的表达式."),
                            errdetail("不支持的表达式类型: %d.", (int)a_expr->kind),
                            errcause("在 START WITH / CONNECT BY 子句中发现不支持的表达式."),
                            erraction("检查并修改您的查询，或联系华为工程师.")));
                    break;
                }
            }
            break;
        }

        case T_A_Const: {
            A_Const *n = (A_Const *)expr;

            int32 val = GetStartWithFakeConstValue(n);
            if (val == CONNECT_BY_LEVEL_FAKEVALUE) {
                context->connect_by_type = CONNECT_BY_LEVEL;
            } else if (val == CONNECT_BY_ROWNUM_FAKEVALUE) {
                context->connect_by_type = CONNECT_BY_ROWNUM;
            }

            break;
        }

        case T_ParamRef: {
            break;
        }

        default: {
            ereport(ERROR,
                (errmodule(MOD_PARSER), errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                    errmsg("在 START WITH / CONNECT BY 子句中发现不支持的表达式."),
                    errdetail("不支持的节点类型: %d.", (int)nodeTag(expr)),
                    errcause("在 START WITH / CONNECT BY 子句中发现不支持的表达式."),
                    erraction("检查并修改您的查询，或联系华为工程师.")));
            break;
        }

    }

    return;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 检查在 SELECT 语句中是否存在不允许的子句
 *    1. 遍历 FROM 子句，检查是否包含 RangeTimeCapsule 或 RangeTableSample，如果包含，则返回 true。
 *    2. 如果存在以上不允许的子句，则返回 true，否则返回 false。
 * --------------------------------------------------------------------------------------
*/
static bool isForbiddenClausesPresent(SelectStmt *stmt)
{
    ListCell* cell = NULL;
    foreach (cell, stmt->fromClause) {
        Node* n = (Node*)lfirst(cell);
        if (IsA(n, RangeTimeCapsule) || IsA(n, RangeTableSample)) {
            return true;
        }
    }
    return false;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 检查 CONNECT BY 子句中的表达式的有效性
 *    1. 尝试替换 CONNECT BY 表达式中的伪值。
 *    2. 如果替换发生，则表示 CONNECT BY 子句中出现了不支持的表达式，抛出错误。
 * --------------------------------------------------------------------------------------
 */
static void checkConnectByExprValidity(Node* connectByExpr)
{
    Node* node = tryReplaceFakeValue(connectByExpr);
    if (node != connectByExpr) {
        ereport(ERROR,
            (errmodule(MOD_PARSER), errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                errmsg("CONNECT BY 子句中发现不支持的表达式。"),
                errdetail("伪列期望一个运算符。"),
                errcause("CONNECT BY 子句中存在不支持的表达式。"),
                erraction("检查并修正您的查询，或联系华为工程师。")));
    }
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 转换 START WITH 子句
 *    1. 如果存在不允许的子句（如 TABLESAMPLE 或 TIMECAPSULE），则抛出错误。
 *    2. 获取 START WITH 子句中的 startWithExpr 和 connectByExpr。
 *    3. 对 connectByExpr 进行伪值替换并检查其有效性。
 *    4. 将 CONNECT BY 子句拆分为两个列表，一个包含 "level" 或 "rownum"，另一个包含其他表达式。
 *    5. 分别构建 connectByLevelExpr 和 connectByExpr。
 *    6. 调用 StartWithWalker 处理 startWithExpr、connectByLevelExpr 和 connectByExpr。
 *    7. 处理可能需要推送的 where 条件，仅处理隐式连接的表。
 *    8. 添加 CONNECT BY 子句中的伪列到 CTE 的输出列。
 * --------------------------------------------------------------------------------------
 */
static void transformStartWithClause(StartWithTransformContext *context, SelectStmt *stmt)
{
    if (stmt == NULL) {
        return;
    }

    // 检查是否存在不允许的子句
    if (isForbiddenClausesPresent(stmt)) {
        ereport(ERROR,
            (errmodule(MOD_PARSER), errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                errmsg("不能在 TABLESAMPLE 或 TIMECAPSULE 中使用 START WITH 或 CONNECT BY。"),
                errdetail("不支持的目标类型"),
                errcause("START WITH 或 CONNECT BY 子句中存在不支持的目标类型。"),
                erraction("检查并修正您的查询，或联系华为工程师。")));
    }

    // 获取 START WITH 子句的信息
    StartWithClause *clause = (StartWithClause *)stmt->startWithClause;
    Node *startWithExpr = clause->startWithExpr;
    Node *connectByExpr = clause->connectByExpr;
    context->connectByExpr = connectByExpr;
    context->startWithExpr = startWithExpr;
    context->connect_by_type = CONNECT_BY_PRIOR;
    context->nocycle = clause->nocycle;
    context->siblingsOrderBy = (List *)clause->siblingsOrderBy;

    // 在 CONNECT BY 子句中进行伪值替换并检查有效性
    raw_expression_tree_walker((Node*)context->connectByExpr,
        (bool (*)())pseudo_level_rownum_walker, (Node*)context->connectByExpr);
    checkConnectByExprValidity((Node*)connectByExpr);
    context->relInfoList = context->pstate->p_start_info;

    // 拆分 CONNECT BY 子句为两个列表
    flattenConnectByExpr(context, connectByExpr);
    context->connectByLevelExpr = buildExprUsingAnd(list_head(context->rownum_or_level_list));
    context->connectByExpr = buildExprUsingAnd(list_head(context->normal_list));

    // 处理 START WITH 子句和 CONNECT BY 子句的表达式
    StartWithWalker(context, startWithExpr);
    StartWithWalker(context, context->connectByLevelExpr);
    StartWithWalker(context, context->connectByExpr);

    /*
     * 处理可能需要推送的 where 条件。
     * 只处理隐式连接的表，因为在我们实现的 START WITH .. CONNECT BY .. 语法中，
     * 在此阶段没有清晰的从非连接条件中划分连接条件的方法。
     * 用户在实现明确的连接表之前应该尽量使用明确的连接表，
     * 在明确的解决方案实现之前，处理隐式连接的表可能会有困难。
     */
    int lens = list_length(context->pstate->p_start_info);
    if (lens != 1) {
        Node *whereClause = (Node *)copyObject(stmt->whereClause);
        context->whereClause = whereClause;
    }

    // 检查是否存在 connectBy_prior_name
    if (startWithExpr != NULL && context->connectby_prior_name == NULL) {
        ereport(ERROR,
                (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                errmsg("START WITH CONNECT BY 子句必须具有至少一个 prior 键。")));
    }
    Assert(context->relInfoList);
    return;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 添加 START WITH CTE 的伪列返回信息到 CTE 对象
 *    1. 遍历 START WITH CTE 的伪列返回信息，将其添加到 CTE 的 target list 中。
 *    2. 对于每个伪列返回信息，构建对应的 Var 节点，并添加到 CTE 的 target list 中。
 *    3. 更新 CTE 的其他属性，包括列名、列类型、列类型修饰符和列排序规则。
 * --------------------------------------------------------------------------------------
 */
void AddStartWithCTEPseudoReturnColumns(CommonTableExpr *cte,
       RangeTblEntry *rte, Index rte_index)
{
    Assert (rte->rtekind == RTE_CTE);

    /* 添加并修正伪列的 TargetEntry */
    /* 步骤 1. 修正 ctequery 的输出 */
    Query *ctequery = (Query *)cte->ctequery;

    /* 添加伪列到 rte->eref->colnames */
    Node        *expr = NULL;
    TargetEntry *tle = NULL;
    StartWithCTEPseudoReturnAtts *att = NULL;
    bool pseudoExist = false;
    ListCell *lc = NULL;

    foreach(lc, ctequery->targetList) {
        TargetEntry *entry = (TargetEntry *)lfirst(lc);
 
        if (IsPseudoReturnTargetEntry(entry)) {
            pseudoExist = true;
            break;
        }
    }

    if (pseudoExist) {
        return;
    }

    for (uint i = 0; i < STARTWITH_PSEUDO_RETURN_ATTNUMS; i++) {
        /* 创建伪列的 TargetEntry 格式 */
        att = &g_StartWithCTEPseudoReturnAtts[i];

        /* 创建伪列的 Var 节点 */
        expr = (Node *)makeVar(rte_index,
                               list_length(ctequery->targetList) + 1,
                               att->coltype,
                               att->coltypmod,
                               att->colcollation, 0);

        /* 创建伪列的 TargetEntry */
        tle = makeTargetEntry((Expr *)expr, list_length(ctequery->targetList) + 1, att->colname, false);
        tle->isStartWithPseudo = true;

        /* 添加伪列到 CTE 的 target list */
        ctequery->targetList = lappend(ctequery->targetList, tle);

        /* 修正 CTE 的相关输出数据结构 */
        rte->eref->colnames = lappend(rte->eref->colnames, makeString(att->colname));
        rte->ctecoltypes = lappend_oid(rte->ctecoltypes, att->coltype);
        rte->ctecoltypmods = lappend_int(rte->ctecoltypmods, att->coltypmod);
        rte->ctecolcollations = lappend_oid(rte->ctecolcollations, att->colcollation);
    }

    return;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 在 CreateStartWithCteInner/OuterBranch() 中的辅助函数，
 *         在 inner/outer 子查询中添加 START WITH CTE 子句
 *    1. 遍历 START WITH CTE 中的每个伪列返回信息。
 *    2. 将其添加到 CTE 子句的 withClause 中。
 * --------------------------------------------------------------------------------------
 */
static void AddWithClauseToBranch(ParseState *pstate, SelectStmt *stmt, List *relInfoList)
{
    ListCell *lc1 = NULL;
    ListCell *lc2 = NULL;
    List *ctes = NIL;

    if (pstate->origin_with == NULL) {
        return;
    }

    // 复制原始 WITH 子句的信息
    WithClause *clause = (WithClause *)copyObject(pstate->origin_with);

    // 遍历 CTE 列表
    foreach(lc1, relInfoList) {
        StartWithTargetRelInfo *info = (StartWithTargetRelInfo *)lfirst(lc1);
        CommonTableExpr *removed = NULL;

        if (info->rtekind != RTE_CTE) {
            continue;
        }

        // 复制当前 WITH 子句的所有 CTE
        foreach(lc2, clause->ctes) {
            CommonTableExpr *cte = (CommonTableExpr *)lfirst(lc2);
            ctes = lappend(ctes, cte);
        }

        // 查找并移除当前 CTE
        foreach(lc2, pstate->p_ctenamespace) {
            CommonTableExpr* cte = (CommonTableExpr*)lfirst(lc2);
 
            if (pg_strcasecmp(cte->ctename, info->relname) == 0) {
                removed = cte;
                break;
            }
        }

        // 移除当前 CTE
        if (removed != NULL) {
            pstate->p_ctenamespace = list_delete(pstate->p_ctenamespace, removed);
        }
    }

    // 如果没有 CTE，则返回
    if (ctes == NULL) {
        return;
    }

    // 更新 WITH 子句的 CTE 列表
    clause->ctes = ctes;
    stmt->withClause = clause;

    return;
}


static bool count_columnref_walker(Node *node, int *columnref_count)
{
    if (node == NULL) {
        return false;
    }

    if (!IsA(node, ColumnRef)) {
        // 如果当前节点不是 ColumnRef 类型，则递归调用 walker
        return raw_expression_tree_walker(node, (bool (*)()) count_columnref_walker, (void*)columnref_count);
    }

    *columnref_count = *columnref_count + 1;

    return false;
}

static bool walker_to_exclude_non_join_quals(Node *node, Node *context_node)
{
    if (node == NULL) {
        return false;
    }

    if (!IsA(node, A_Expr)) {
        // 如果当前节点不是 A_Expr 类型，则递归调用 walker
        return raw_expression_tree_walker(node, (bool (*)()) walker_to_exclude_non_join_quals, (void*)NULL);
    }

    A_Expr* expr = (A_Expr*) node;
    if (expr->kind != AEXPR_OP) {
        // 如果 A_Expr 不是 AEXPR_OP 类型，则递归调用 walker
        return raw_expression_tree_walker(node, (bool (*)()) walker_to_exclude_non_join_quals, (void*)NULL);
    }

    /*
     * 这是为了与原始的 start with .. connect by 语法产生的结果集保持一致，
     * 该语法不会将过滤条件推送到连接条件中。
     * 如果 AEXPR_OP 中没有超过一个列项，我们猜测它不是连接条件，
     * 因此不应在 SW 操作中过滤它，并强制将其设置为 true。
     * 这个规则并不总是正确，但在大多数情况下应该工作得很好。
     * 以后可以进行改进，例如找到更好的方法从 where 子句中提取非连接条件。
     */
    int columnref_count = 0;
    (void) raw_expression_tree_walker(node, (bool (*)()) count_columnref_walker, (void*)&columnref_count);

    if (columnref_count <= 1) {
        expr->lexpr = makeBoolAConst(true, -1);
        expr->rexpr = makeBoolAConst(true, -1);
        expr->kind = AEXPR_OR;
    }

    return false;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 创建 SWCB 转换后的 CTE 内部分支，通常我们会将 ConnectByExpr 添加到内部分支的 joincond 中
 *
 * @param:
 *    - (1). pstate: 当前 SWCB 所属查询级别的 parseState
 *    - (2). context: 当前 SWCB 的转换上下文
 *    - (3). relInfoList: SWCB 的关联基本 RangeVar
 *    - (4). connectByExpr: connectby 子句的表达式将被放置为 RQ 的连接条件
 *    - (5). whereClause: where 子句的表达式
 *
 * @Return: 输入
 * --------------------------------------------------------------------------------------
 */
static SelectStmt *CreateStartWithCTEInnerBranch(ParseState* pstate,
                        StartWithTransformContext *context,
                        List *relInfoList,
                        Node *connectByExpr,
                        Node *whereClause)
{
    Node *origin_table = NULL;
    SelectStmt *result = makeNode(SelectStmt);
    JoinExpr *join = makeNode(JoinExpr);
    RangeVar *work_table = makeRangeVar(NULL, "tmp_reuslt", -1);

    AddWithClauseToBranch(pstate, result, relInfoList);

    if (list_length(relInfoList) == 1) {
        StartWithTargetRelInfo *info = (StartWithTargetRelInfo *)linitial(relInfoList);
        origin_table = (Node *)copyObject(info->tblstmt);
    } else {
        ListCell *lc = NULL;

        List *fromClause = (List *)copyObject(context->fromClause);
        foreach(lc, fromClause) {
            Node *node = (Node *)lfirst(lc);

            if (origin_table == NULL) {
                origin_table = node;
                continue;
            }

            /* 创建新的 JoinExpr */
            Node *qual = makeBoolAConst(true, -1);
            JoinExpr *joiniter = makeNode(JoinExpr);

            joiniter->larg = origin_table;
            joiniter->rarg = node;
            joiniter->quals = qual;

            origin_table = (Node *)joiniter;
        }

        if (whereClause != NULL) {
            JoinExpr *final_join = (JoinExpr *)origin_table;
            /* 推送下需要深度复制 quals */
            Node *whereCopy = (Node *)copyObject(whereClause);
            /* 只有连接 quals 可以被推送下去 */
            raw_expression_tree_walker((Node *)whereCopy,
                (bool (*)())walker_to_exclude_non_join_quals, (void*)NULL);

            if (final_join->quals == NULL) {
                final_join->quals = whereCopy;
            } else {
                final_join->quals =
                    (Node *)makeA_Expr(AEXPR_AND, NULL, whereCopy, final_join->quals, -1);
            }
        }
    }

    /* 处理 regular/level */
    switch (context->connect_by_type) {
        case CONNECT_BY_PRIOR:
        case CONNECT_BY_ROWNUM:
        case CONNECT_BY_LEVEL:
        case CONNECT_BY_MIXED_LEVEL:  {
            join->jointype = JOIN_INNER;
            join->isNatural = FALSE;
            join->larg = (Node *)work_table;
            join->rarg = origin_table;
            join->usingClause = NIL;
            join->quals = (Node *)copyObject(connectByExpr);
            result->targetList = expandAllTargetList(relInfoList);
            result->fromClause = list_make1(join);

            break;
        }
        default: {
            elog(ERROR, "未识别的 connect by 类型 %d", context->connect_by_type);
        }
    }

    return result;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 创建 SWCB 转换后的 CTE 外部分支，通常我们会将 StartWithExpr 添加到外部分支的过滤条件中
 *
 * @param:
 *    - (1). pstate: 当前 SWCB 所属查询级别的 parseState
 *    - (2). context: 当前 SWCB 的转换上下文
 *    - (3). relInfoList: SWCB 的关联基本 RangeVar
 *    - (4). startWithExpr: start with 子句的表达式将被放置为 RQ 的初始条件
 *    - (5). whereClause: where 子句的表达式
 *
 * @Return: 输入
 * --------------------------------------------------------------------------------------
 */
static SelectStmt *CreateStartWithCTEOuterBranch(ParseState *pstate,
                                                    StartWithTransformContext *context,
                                                    List *relInfoList,
                                                    Node *startWithExpr,
                                                    Node *whereClause)
{
    ListCell *lc = NULL;
    List *targetlist = NIL;
    List *tblist = NIL;
    Node *quals = NULL;

    SelectStmt *result = makeNode(SelectStmt);

    AddWithClauseToBranch(pstate, result, relInfoList);

    /* 形成 targetlist */
    targetlist = expandAllTargetList(relInfoList);

    if (context->fromClause != NULL) {
        tblist = (List *)copyObject(context->fromClause);
    } else {
        foreach(lc, relInfoList) {
            StartWithTargetRelInfo *info = (StartWithTargetRelInfo *)lfirst(lc);
            tblist = lappend(tblist, copyObject(info->tblstmt));
        }
    }

    /* 推送 whereClause 到 init 部分，注意避免在表达式中出现 NULL。 */
    quals = (Node *)startWithExpr;
    Node* whereClauseCopy = (Node *)copyObject(whereClause);
    if (whereClause != NULL) {
        /* 只有连接 quals 可以被推送下去 */
        raw_expression_tree_walker((Node*)whereClauseCopy,
            (bool (*)())walker_to_exclude_non_join_quals, (void*)NULL);
    }

    if (quals == NULL) {
        quals = whereClauseCopy;
    } else if (whereClause != NULL) {
        quals = (Node *)makeA_Expr(AEXPR_AND, NULL, whereClauseCopy,
            (Node*)startWithExpr, -1);
    }

    result->fromClause = tblist;
    result->whereClause = quals;
    result->targetList = targetlist;

    return result;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 将递归部分和非递归部分转换为递归 UNION 操作
 * --------------------------------------------------------------------------------------
 */
static void CreateStartWithCTE(ParseState *pstate, Query *qry,
                   SelectStmt *initpart, SelectStmt *workpart, StartWithTransformContext *context)
{
    // 创建 UNION 查询
    SelectStmt *setop = makeNode(SelectStmt);
    setop->op = SETOP_UNION;
    setop->all = true;
    setop->larg = initpart;
    setop->rarg = workpart;

    // 创建 Common Table Expression (CTE)
    CommonTableExpr *common_expr = makeNode(CommonTableExpr);
    common_expr->swoptions = makeNode(StartWithOptions);
    common_expr->ctename = "tmp_reuslt";
    common_expr->ctequery = (Node *)setop;
    common_expr->swoptions->siblings_orderby_clause = context->siblingsOrderBy;
    common_expr->swoptions->connect_by_type = context->connect_by_type;

    /*
     *  CTE 在这个阶段还不可用，因此我们通过对 p_hasStartWith 的操作来禁用 "start with" 类型的列引用转换，
     *  以避免引发列未找到的错误
     */
    pstate->p_hasStartWith = false;
    common_expr->swoptions->connect_by_level_quals =
        transformWhereClause(pstate, context->connectByLevelExpr, EXPR_KIND_SELECT_TARGET, "LEVEL/ROWNUM quals");

    /* 需要修复连接条件中的排序规则 */
    assign_expr_collations(pstate, common_expr->swoptions->connect_by_level_quals);

    pstate->p_hasStartWith = true;

    common_expr->swoptions->connect_by_other_quals = context->connectByOtherExpr;
    common_expr->swoptions->nocycle = context->nocycle;

    WithClause *with_clause = makeNode(WithClause);
    with_clause->ctes = NULL;
    with_clause->recursive = true;

    with_clause->ctes = lappend(with_clause->ctes, common_expr);

    /* 用于多级 "start with...connect by" */
    pstate->p_sw_selectstmt->withClause = (WithClause *)copyObject(with_clause);
    pstate->p_sw_selectstmt->startWithClause = NULL;

    /* 备份并恢复 p_ctenamespace */
    List *p_ctenamespace = pstate->p_ctenamespace;
    pstate->p_ctenamespace = NULL;

    qry->hasRecursive = with_clause->recursive;
    qry->cteList = transformWithClause(pstate, with_clause);
    qry->hasModifyingCTE = pstate->p_hasModifyingCTE;

    pstate->p_ctenamespace = list_concat_unique(pstate->p_ctenamespace, p_ctenamespace);
    list_free_ext(p_ctenamespace);

    return;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 详细信息待添加
 * --------------------------------------------------------------------------------------
 */
static RangeTblEntry *transformStartWithCTE(ParseState* pstate, List *prior_names)
{
    ListCell *lc = NULL;
    Index ctelevelsup = 0;
    RangeTblEntry* rte = makeNode(RangeTblEntry);

    // 扫描命名空间以获取 CTE
    CommonTableExpr *cte = scanNameSpaceForCTE(pstate, "tmp_reuslt", &ctelevelsup);

    Assert(cte != NULL);

    rte->rtekind = RTE_CTE;
    rte->ctename = cte->ctename;
    rte->relname = cte->ctename;
    rte->ctelevelsup = ctelevelsup;
    rte->inh = false;
    rte->inFromCl = true;

    // 如果 CTE 不是自引用，增加引用计数
    rte->self_reference = !IsA(cte->ctequery, Query);
    if (!rte->self_reference) {
        cte->cterefcount++;
    }

    rte->ctecoltypes = cte->ctecoltypes;
    rte->ctecoltypmods = cte->ctecoltypmods;
    rte->ctecolcollations = cte->ctecolcollations;

    Alias* eref = makeAlias(cte->ctename, NIL);
    Alias* alias = makeAlias(cte->ctename, NIL);

    // 将列名添加到 eref 中
    foreach(lc, cte->ctecolnames) {
        eref->colnames = lappend(eref->colnames, lfirst(lc));
    }

    rte->eref = eref;
    rte->alias = alias;

    int index = 0;
    List *key_index = NIL;

    // 遍历 CTE 的列名，根据传入的 prior_names 列表确定 key_index
    foreach(lc, cte->ctecolnames) {
        Value *colname = (Value *)lfirst(lc);

        if (list_member(prior_names, colname)) {
            key_index = lappend_int(key_index, index);
        }

        index++;
    }

    // 设置 CTE 中的 prior_key_index
    cte->swoptions->prior_key_index = key_index;

    /*
     * 为原始的 SelectStmt 填充一些重写信息，
     * 这样它可以在下一步的重写中被上层使用
     */
    foreach(lc, pstate->p_sw_selectstmt->withClause->ctes) {
        CommonTableExpr* common = (CommonTableExpr*)lfirst(lc);

        if (strcmp(common->ctename, "tmp_reuslt") == 0) {
            common->swoptions->prior_key_index = key_index;
            break;
        }
    }

    /* 将重写后的 RTE 添加到 p_rtable 中 */
    pstate->p_rtable = lappend(pstate->p_rtable, rte);

    // 向 CTE 中添加伪返回列
    AddStartWithCTEPseudoReturnColumns(cte, rte, list_length(pstate->p_rtable));

    return rte;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 将查询的FROM列表转换为递归查询的两个分支：非递归部分和递归部分
 *
 * @param:
 *    - (1). pstate，解析状态
 *    - (2). qry，查询
 *    - (3). context，转换上下文
 *    - (4). n，FROM列表的树形结构
 *
 * @Return: 无
 * --------------------------------------------------------------------------------------
 */
static void transformFromList(ParseState* pstate, Query* qry,
                        StartWithTransformContext *context, Node *n)
{
    ListCell *lc = NULL;
    A_Expr *startWithExpr = (A_Expr *)context->startWithExpr;
    A_Expr *connectByExpr = (A_Expr *)context->connectByExpr;
    List *relInfoList = context->relInfoList;
    Node *whereClause = context->whereClause;

    /* 创建 UNION ALL 分支用于非递归部分 */
    SelectStmt *outerBranch = CreateStartWithCTEOuterBranch(pstate, context,
                        relInfoList, (Node *)startWithExpr, whereClause);

    /* 创建 JoinExpr 用于递归部分 */
    SelectStmt *innerBranch = CreateStartWithCTEInnerBranch(pstate, context,
                        relInfoList, (Node *)connectByExpr, whereClause);

    /* 创建递归 UNION 查询和 Common Table Expression */
    CreateStartWithCTE(pstate, qry, outerBranch, innerBranch, context);

    /*
     * 最终需要修复 RTE 位置，将其中一个 start_with_rtes 替换为 CTE
     **/
    foreach(lc, relInfoList) {
        StartWithTargetRelInfo *info = (StartWithTargetRelInfo *)lfirst(lc);
        RangeTblEntry* rte = info->rte;
        RangeTblRef *rtr = info->rtr;

        pstate->p_joinlist = list_delete(pstate->p_joinlist, rtr);

        /* 从 p_varnamespace 删除 */
        ListCell *lcc = NULL;
        ParseNamespaceItem *nsitem = NULL;
        foreach(lcc, pstate->p_varnamespace) {
            ParseNamespaceItem *sitem = (ParseNamespaceItem *)lfirst(lcc);

            if (sitem->p_rte == rte) {
                nsitem = sitem;
                break;
            }
        }
        pstate->p_varnamespace = list_delete(pstate->p_varnamespace, nsitem);
    }

    RangeTblEntry *replace = transformStartWithCTE(pstate, context->connectby_prior_name);
    int rtindex = list_length(pstate->p_rtable);
    RangeTblRef *rtr = makeNode(RangeTblRef);
    rtr->rtindex = rtindex;
    replace->swConverted = true;
    replace->origin_index = list_make1_int(rtr->rtindex);

    pstate->p_joinlist = list_make1(rtr);
    pstate->p_varnamespace = list_make1(makeNamespaceItem(replace, false, true));
    pstate->p_relnamespace = lappend(pstate->p_relnamespace,
                                    makeNamespaceItem(replace, false, true));

    return;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 将单个 RangeTblEntry（RTE）转换为递归查询的两个分支：非递归部分和递归部分
 *
 * @param:
 *    - (1). pstate，解析状态
 *    - (2). qry，查询
 *    - (3). context，转换上下文
 *    - (4). start_clause，开始子句的树形结构
 *
 * @Return: 无
 * --------------------------------------------------------------------------------------
 */
static void transformSingleRTE(ParseState* pstate, Query* qry,
           StartWithTransformContext *context, Node *start_clause)
{
    ListCell *lc = NULL;

    A_Expr *connectByExpr = (A_Expr *)context->connectByExpr;
    A_Expr *startWithExpr = (A_Expr *)context->startWithExpr;
    List *startWithRelInfoList = context->relInfoList;

    StartWithTargetRelInfo *info = (StartWithTargetRelInfo *)linitial(context->relInfoList);

    /* 创建非递归部分的 SELECT 语句 */
    SelectStmt *outerBranch = CreateStartWithCTEOuterBranch(pstate, context,
                            startWithRelInfoList, (Node *)startWithExpr, NULL);

    /* 创建递归部分的 SELECT 语句 */
    SelectStmt *innerBranch = CreateStartWithCTEInnerBranch(pstate, context,
                            startWithRelInfoList, (Node *)connectByExpr, NULL);

    /* 创建递归 UNION 查询和 Common Table Expression */
    CreateStartWithCTE(pstate, qry, outerBranch, innerBranch, context);

    /* 找到原始 RTE，然后用新的 CTE 替换它 */
    RangeTblEntry* rte = info->rte;
    RangeTblRef *rtr = info->rtr;
    pstate->p_joinlist = list_delete(pstate->p_joinlist, rtr);

    // 从 p_varnamespace 中删除
    ParseNamespaceItem *nsitem = NULL;
    foreach(lc, pstate->p_varnamespace) {
        ParseNamespaceItem *sitem = (ParseNamespaceItem *)lfirst(lc);

        if (sitem->p_rte == rte) {
            nsitem = sitem;
            break;
        }
    }
    pstate->p_varnamespace = list_delete(pstate->p_varnamespace, nsitem);

    RangeTblEntry *replace = transformStartWithCTE(pstate, context->connectby_prior_name);
    replace->swConverted = true;
    replace->origin_index = list_make1_int(info->rtr->rtindex);
    int rtindex = list_length(pstate->p_rtable);
    rtr = makeNode(RangeTblRef);
    rtr->rtindex = rtindex;

    pstate->p_joinlist = lappend(pstate->p_joinlist, rtr);
    pstate->p_varnamespace = lappend(pstate->p_varnamespace,
                                     makeNamespaceItem(replace, false, true));
    pstate->p_relnamespace = lappend(pstate->p_relnamespace,
                                     makeNamespaceItem(replace, false, true));

    return;
}

/*
 * --------------------------------------------------------------------------------------
 * @Brief: 展开所有的目标列，以适应递归查询的两个分支
 *
 * @param:
 *    - (1). targetRelInfoList，目标列信息的列表
 *
 * @Return: 目标列的列表
 * --------------------------------------------------------------------------------------
 */
static List *expandAllTargetList(List *targetRelInfoList)
{
    ListCell *lc1 = NULL;
    ListCell *lc2 = NULL;
    List *targetlist = NIL;

    foreach(lc1, targetRelInfoList) {
        StartWithTargetRelInfo *info = (StartWithTargetRelInfo *)lfirst(lc1);
        RangeTblEntry *rte = info->rte;

        /* 用表别名转换目标列 */
        char *relname = NULL;
        Alias *alias = rte->eref;

        if (info->rtekind == RTE_SUBQUERY) {
            relname = info->aliasname;
        } else if (info->rtekind == RTE_RELATION) {
            relname = info->aliasname ? info->aliasname : info->relname;
        } else if (info->rtekind == RTE_CTE) {
            relname = info->aliasname ? info->aliasname : info->relname;
        }

        foreach(lc2, alias->colnames) {
            Value *val = (Value *)lfirst(lc2);

            ColumnRef *column = makeNode(ColumnRef);
            char *colname = strVal(val);

            /* 跳过已删除的列，其中附加了表别名."" */
            if (strlen(colname) == 0) {
                continue;
            }

            ResTarget *target = makeNode(ResTarget);

            column->fields = list_make2(makeString(relname), val);
            column->location = -1;
            target->val = (Node *)column;
            target->location = -1;

            target->name = makeStartWithDummayColname(relname, colname);
            targetlist = lappend(targetlist, target);
        }
    }

    return targetlist;
}

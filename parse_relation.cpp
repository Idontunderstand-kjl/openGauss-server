/* -------------------------------------------------------------------------
 *
 * parse_relation.cpp
 *	  parser support routines dealing with relations
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/common/backend/parser/parse_relation.cpp
 *
 * -------------------------------------------------------------------------
 */
#include "postgres.h"
#include "knl/knl_variable.h"

#include <ctype.h>

#include "access/sysattr.h"
#include "access/tableam.h"
#include "catalog/heap.h"
#include "catalog/namespace.h"
#include "catalog/pg_auth_history.h"
#include "catalog/pg_type.h"
#include "funcapi.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "parser/parsetree.h"
#include "parser/parse_hint.h"
#include "parser/parse_relation.h"
#include "parser/parse_type.h"
#include "parser/parse_clause.h"
#include "parser/parse_expr.h"
#ifdef PGXC
#include "access/transam.h"
#include "pgxc/pgxc.h"
#endif
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/partitionkey.h"
#include "utils/rel.h"
#include "utils/rel_gs.h"
#include "utils/syscache.h"
#include "utils/pl_package.h"
#include "catalog/pg_partition_fn.h"
#include "catalog/pg_synonym.h"
#include "parser/parse_utilcmd.h"
#include "parser/parse_expr.h"
#include "commands/tablecmds.h"
#include "catalog/pg_user_status.h"
#include "commands/user.h"
#include "utils/snapmgr.h"
#include "workload/workload.h"
#include "storage/lmgr.h"
#include "tcop/utility.h"
#include "optimizer/bucketinfo.h"
#include "optimizer/planner.h"
#include "storage/tcap.h"
#include "gs_ledger/ledger_utils.h"
#include "catalog/pg_object.h"
#include "catalog/pg_depend.h"
#include "catalog/pg_rewrite.h"
#ifdef ENABLE_MOT
#include "storage/mot/jit_def.h"
#endif

#define MAXSTRLEN ((1 << 11) - 1)
static RangeTblEntry* scanNameSpaceForRefname(ParseState* pstate, const char* refname, int location);
// 在命名空间中扫描引用名称，返回匹配的范围表条目

static RangeTblEntry* scanNameSpaceForRelid(ParseState* pstate, Oid relid, int location);
// 在命名空间中扫描关系 ID，返回匹配的范围表条目

static void markRTEForSelectPriv(ParseState* pstate, RangeTblEntry* rte, int rtindex, AttrNumber col);
// 标记范围表条目的列以进行选择权限检查

static void expandRelation(Oid relid, Alias* eref, int rtindex, int sublevels_up, int location, bool include_dropped, List** colnames, List** colvars);
// 展开给定关系的列，填充传入的 colnames 和 colvars 列表

static void expandTupleDesc(TupleDesc tupdesc, Alias* eref, int rtindex, int sublevels_up, int location, bool include_dropped, List** colnames, List** colvars);
// 展开给定元组描述符的列，填充传入的 colnames 和 colvars 列表

static void setRteOrientation(Relation rel, RangeTblEntry* rte);
// 设置范围表条目的方向，通常与复杂类型（例如表的分区）相关

static int32* getValuesTypmods(RangeTblEntry* rte);
// 获取范围表条目的类型修饰符数组

static IndexHintType preCheckIndexHints(ParseState* pstate, List* indexhints, Relation relation);
// 在解析之前对索引提示进行预检查，返回索引提示的类型

#ifndef PGXC
static int specialAttNum(const char* attname);
// 如果未定义 PGXC，声明一个静态函数 specialAttNum，该函数接受属性名称并返回特殊属性的数字
#endif

// 替换在字符串 label 中出现的 CTE 别名中的 '@' 后的部分。
static char *ReplaceSWCTEOutSrting(ParseState *pstate, RangeTblEntry *rte, char *label)
{
    ListCell *lc = NULL;
    char *result = NULL;
    char *relname = NULL;

    // 遍历原始索引列表
    foreach (lc, rte->origin_index) {
        int index = (int)lfirst_int(lc);
        RangeTblEntry *old_rte = (RangeTblEntry *)list_nth(pstate->p_rtable, index - 1);

        // 获取关系名称（表名或子查询别名）
        if (old_rte->rtekind == RTE_RELATION || old_rte->rtekind == RTE_CTE) {
            relname = old_rte->relname;
        } else if (old_rte->rtekind == RTE_SUBQUERY) {
            relname = old_rte->alias->aliasname;
        }

        /* 替换 CTE 别名中的 '@' 后的部分 */
        if (strrchr(label, '@')) {
            label = strrchr(label, '@');
            label += 1;
        }
    }

    // 复制替换后的字符串，作为结果返回
    result = pstrdup(label);
    return result;
}


/*
 * @Description:  设置 RangeTblEntry 结构体的不同标志。以下是标志的含义
 * @inout rte: 指向RTE的指针
 * @in: 是否继承
 * @in inFromCl: 是否在FROM子句中出现
 * @in perm: 所需权限，如ACL_SELECT等
 */
static void set_rte_flags(RangeTblEntry* rte, bool inh, bool inFromCl, int perm)
{
    /* ----------
     * Flags:
     * - this RTE should be expanded to include descendant tables,
     * - this RTE is in the FROM clause,
     * - this RTE should be checked for appropriate access rights.
     *
     * Joins are never checked for access rights.
     * ----------
     */
    rte->inh = inh; /* never true for joins */
    rte->inFromCl = inFromCl;

    rte->requiredPerms = perm;
    rte->checkAsUser = InvalidOid;
    rte->selectedCols = NULL;
    rte->insertedCols = NULL;
    rte->updatedCols = NULL;
    rte->extraUpdatedCols = NULL;
}

/*
 * @Description: 获取有效关系的分区属性编号列表。
 * @in rel: 关系
 * @return: 一个属性编号列表
 */
static List* get_rte_part_attr_num(Relation rel)
{
    // 如果是 PGXC 协调节点（coordinator）且关系是有效的普通对象
    // 且关系有有效的定位器信息（locator_info）
    if (IS_PGXC_COORDINATOR && rel->rd_id >= FirstNormalObjectId && PointerIsValid(rel->rd_locator_info)) {
        // 返回关系的定位器信息中的分区属性编号列表的副本
        return (List*)copyObject(rel->rd_locator_info->partAttrNum);
    }

    // 否则返回空列表
    return NULL;
}

/*
 * refnameRangeTblEntry
 *	  给定可能带有限定符的引用名称，查看它是否与任何RTE匹配。
 *	  如果匹配，则返回指向RangeTblEntry的指针；否则返回NULL。
 *
 *	  可选择地获取RTE的嵌套深度（0 = 当前）存储在 *sublevels_up 中。
 *	  如果 sublevels_up 为 NULL，则只考虑当前嵌套级别的条目。
 *
 * 一个未限定的引用名称（schemaname == NULL）可以匹配任何带有匹配别名的RTE，
 * 或者在没有别名的关系RTE的情况下，可以匹配带有匹配未限定relname的RTE。
 * 可能会出现这样的情况，使得引用名称在最近的嵌套级别中匹配多个RTE；
 * 如果是这样，我们通过 ereport() 报告一个错误。
 *
 * 一个限定的引用名称（schemaname != NULL）只能匹配一个没有别名的关系RTE，
 * 且为与 schemaname.refname 标识的相同关系。在这种情况下，我们将 schemaname.refname 转换为关系 OID，
 * 然后按 relid 而不是别名名称搜索。这可能有点奇怪，但这是 SQL92 规定的操作。
 */
RangeTblEntry* refnameRangeTblEntry(
    ParseState* pstate, const char* schemaname, const char* refname, int location, int* sublevels_up)
{
     Oid relId = InvalidOid;

    // 如果 sublevels_up 不为 NULL，将其初始化为 0
    if (sublevels_up != NULL) {
        *sublevels_up = 0;
    }

    // 如果引用名称带有模式限定符，处理模式名称
    if (schemaname != NULL) {
        Oid namespaceId;

        /*
         * 我们可以在这里使用 LookupNamespaceNoError()，因为我们只关心找到的RTE。
         * 在创建RTE时，检查模式的 USAGE 权限是不必要的。
         * 此外，如果名称匹配用户无权访问的模式名称，我们想报告 "RTE未找到"，而不是 "对模式没有权限"。
         */
        namespaceId = LookupNamespaceNoError(schemaname);
        if (!OidIsValid(namespaceId)) {
            return NULL;
        }
        (void)get_relname_relid_extend(refname, namespaceId, &relId, true, NULL);
        if (!OidIsValid(relId)) {
            return NULL;
        }
    }

    // 在解析状态链中进行循环
    while (pstate != NULL) {
        RangeTblEntry* result = NULL;

        // 根据是否有关系 OID，选择调用不同的函数进行查找
        if (OidIsValid(relId)) {
            result = scanNameSpaceForRelid(pstate, relId, location);
        } else {
            result = scanNameSpaceForRefname(pstate, refname, location);
        }

        // 如果找到匹配的 RangeTblEntry，返回该指针
        if (result != NULL) {
            return result;
        }

        // 如果 sublevels_up 不为 NULL，每次循环中，嵌套深度计数加一
        if (sublevels_up != NULL) {
            (*sublevels_up)++;
        } else {
            // 如果 sublevels_up 为 NULL，表示只考虑当前嵌套级别的条目，直接退出循环
            break;
        }

        // 移动到上一级解析状态
        pstate = pstate->parentParseState;
    }

    // 循环结束仍未找到匹配的 RangeTblEntry，返回 NULL
    return NULL;
}

/*
 * 在查询的表命名空间中搜索与给定未限定引用名称匹配的RTE。
 * 如果找到唯一匹配，则返回该RTE；如果没有匹配，则返回NULL。
 * 如果存在多个匹配，引发错误。
 *
 * @param pstate: 解析状态，包含了当前查询的上下文信息。
 * @param refname: 未限定引用名称，即待匹配的引用标识符。
 * @param location: 引用名称在查询字符串中的位置。
 *
 * @return: 如果找到唯一匹配，返回该RTE；如果没有匹配，返回NULL。
 *          如果存在多个匹配，引发错误。
 */
static RangeTblEntry* scanNameSpaceForRefname(ParseState* pstate, const char* refname, int location)
{
    RangeTblEntry* result = NULL;
    ListCell* l = NULL;

    // 遍历解析状态中的表命名空间
    foreach (l, pstate->p_relnamespace) {
        ParseNamespaceItem *nsitem = (ParseNamespaceItem *) lfirst(l);
        RangeTblEntry *rte = nsitem->p_rte;

        /* 如果不在LATERAL中，忽略仅LATERAL的条目 */
        if (nsitem->p_lateral_only && !pstate->p_lateral_active)
            continue;

        // 比较RTE的别名是否与给定的引用名称匹配
        if (strcmp(rte->eref->aliasname, refname) == 0) {
            // 如果已经找到一个匹配，引发错误
            if (result != NULL)
                ereport(ERROR,
                    (errcode(ERRCODE_AMBIGUOUS_ALIAS),
                        errmsg("table reference \"%s\" is ambiguous", refname),
                        parser_errposition(pstate, location)));
            /* SQL:2008要求这是一个错误，而不是不可见的项 */
            if (nsitem->p_lateral_only && !nsitem->p_lateral_ok)
                ereport(ERROR,
                    (errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
                    errmsg("invalid reference to FROM-clause entry for table \"%s\"", refname),
                    errdetail("The combining JOIN type must be INNER or LEFT for a LATERAL reference."),
                    parser_errposition(pstate, location)));
            // 记录找到的RTE
            result = rte;
        }
    }

    /* 处理 start with...connect by，将结果替换为CTE */
    if (result != NULL && pstate->p_hasStartWith && result->swAborted) {
        foreach(l, pstate->p_rtable) {
            RangeTblEntry *tbl = (RangeTblEntry *)lfirst(l);

            if (tbl->swConverted) {
                result = tbl;
                break;
            }
        }
    }

    // 返回找到的RTE，可能是唯一匹配或者NULL
    return result;
}

/*
 * scanNameSpaceForRelid
 * 在查询的表命名空间中搜索与给定关系OID匹配的关系RTE。
 * 如果找到唯一匹配，返回该RTE；如果没有匹配，返回NULL。
 * 如果存在多个匹配，引发错误（在正确检查命名空间时不应发生）。
 *
 * 请参阅 refnameRangeTblEntry 的注释，了解此函数的操作方式。
 */
static RangeTblEntry* scanNameSpaceForRelid(ParseState* pstate, Oid relid, int location)
{
    RangeTblEntry* result = NULL;
    ListCell* l = NULL;

    // 遍历解析状态中的表命名空间
    foreach (l, pstate->p_relnamespace) {
        ParseNamespaceItem *nsitem = (ParseNamespaceItem *) lfirst(l);
        RangeTblEntry *rte = nsitem->p_rte;

        // 如果不在LATERAL中，忽略仅LATERAL的条目
        if (nsitem->p_lateral_only && !pstate->p_lateral_active)
            continue;

        // 是关系RTE且关系OID匹配
        if (rte->rtekind == RTE_RELATION && rte->relid == relid && rte->alias == NULL) {
            // 如果已经找到一个匹配，引发错误
            if (result != NULL)
                ereport(ERROR,
                    (errcode(ERRCODE_AMBIGUOUS_ALIAS),
                        errmsg("table reference %u is ambiguous", relid),
                        parser_errposition(pstate, location)));
            /* SQL:2008要求这是一个错误，而不是不可见的项 */
            if (nsitem->p_lateral_only && !nsitem->p_lateral_ok)
                ereport(ERROR,
                        (errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
                        errmsg("invalid reference to FROM-clause entry for table \"%s\"", rte->eref->aliasname),
                        errdetail("The combining JOIN type must be INNER or LEFT for a LATERAL reference."),
                        parser_errposition(pstate, location)));
            result = rte;
        }
    }
    return result;
}

/*
 * scanNameSpaceForCTE
 * 在查询的CTE命名空间中搜索与给定未限定引用名称匹配的CTE。
 * 返回CTE（及其levelsup计数）如果有匹配，如果没有匹配则返回NULL。
 * 我们不必担心多个匹配，因为 parse_cte.c 拒绝包含重复CTE名称的WITH列表。
 */
CommonTableExpr* scanNameSpaceForCTE(ParseState* pstate, const char* refname, Index* ctelevelsup)
{
    Index levelsup;

    // 从当前解析状态开始循环
    for (levelsup = 0; pstate != NULL; pstate = pstate->parentParseState, levelsup++) {
        ListCell* lc = NULL;

        // 遍历解析状态中的CTE命名空间
        foreach (lc, pstate->p_ctenamespace) {
            CommonTableExpr* cte = (CommonTableExpr*)lfirst(lc);

            // 找到匹配的CTE
            if (strcmp(cte->ctename, refname) == 0) {
                *ctelevelsup = levelsup;
                return cte;
            }
        }
    }
    return NULL;
}

/*
 * isFutureCTE
 * 搜索可能的 "未来CTE"，即尚未按WITH作用域规则在范围内的CTE。
 * 这与有效的SQL语义无关，但对于错误报告很重要。
 */
static bool isFutureCTE(ParseState* pstate, const char* refname)
{
    // 从当前解析状态开始循环
    for (; pstate != NULL; pstate = pstate->parentParseState) {
        ListCell* lc = NULL;

        // 遍历解析状态中的未来CTE列表
        foreach (lc, pstate->p_future_ctes) {
            CommonTableExpr* cte = (CommonTableExpr*)lfirst(lc);

            // 找到匹配的未来CTE
            if (strcmp(cte->ctename, refname) == 0) {
                return true;
            }
        }
    }
    return false;
}

/*
 * searchRangeTableForRel
 * 看看是否有任何RangeTblEntry可能匹配RangeVar。
 * 如果是，返回指向RangeTblEntry的指针；否则返回NULL。
 * 这与 refnameRangeTblEntry 不同，因为它考虑ParseState的rangetable(s)中的每个条目，
 * 而不仅仅是当前在p_relnamespace列表中可见的那些。
 * 这种行为无效，违反了SQL规范，并且可能会产生模糊的结果
 * （可能存在多个同样有效的匹配，但只返回一个）。
 * 这只能作为给出合适的错误消息的启发式方法使用。参见 errorMissingRTE。
 */
static RangeTblEntry* searchRangeTableForRel(ParseState* pstate, RangeVar* relation)
{
    const char* refname = relation->relname;
    Oid relId = InvalidOid;
    CommonTableExpr* cte = NULL;
    Index ctelevelsup = 0;
    Index levelsup;

    /*
     * 如果是未限定的名称，检查可能的CTE匹配。CTE会隐藏任何真实关系的匹配。
     * 如果没有CTE，查找匹配的关系。
     *
     * 注意：这里不关心 RangeVarGetRelid 在并发DDL情况下返回的正确答案。
     * 如果不正确，最坏的情况是一个不太清晰的错误消息。此外，查询中涉及的表已被锁定，
     * 这减少了出现意外行为的情况。因此，我们在未锁定的情况下进行名称查找。
     */
    if (!relation->schemaname) {
        cte = scanNameSpaceForCTE(pstate, refname, &ctelevelsup);
    }
    if (cte == NULL) {
        relId = RangeVarGetRelid(relation, NoLock, true);
    }

    /* 现在查找匹配的RTE，无论是关系/CTE还是别名 */
    for (levelsup = 0; pstate != NULL; pstate = pstate->parentParseState, levelsup++) {
        ListCell* l = NULL;

        // 遍历解析状态中的rangetable
        foreach (l, pstate->p_rtable) {
            RangeTblEntry* rte = (RangeTblEntry*)lfirst(l);

            // 是关系RTE且关系OID匹配
            if (rte->rtekind == RTE_RELATION && OidIsValid(relId) && rte->relid == relId) {
                return rte;
            }
            // 是CTE Rte且CTE匹配
            if (rte->rtekind == RTE_CTE && cte != NULL && rte->ctelevelsup + levelsup == ctelevelsup &&
                strcmp(rte->ctename, refname) == 0) {
                return rte;
            }
            // 别名匹配
            if (strcmp(rte->eref->aliasname, refname) == 0) {
                return rte;
            }
        }
    }
    return NULL;
}


/*
 * 检查两个 relnamespace 列表之间是否存在表名冲突。
 * 如果有冲突，则抛出错误。
 *
 * 注意：我们假设每个给定的参数本身不包含冲突，
 * 我们只是想知道这两个是否可以合并。
 *
 * 根据 SQL92 标准，两个没有别名的普通关系 RTE（RangeTblEntry）
 * 即使它们有相同的 eref->aliasname（即相同的关系名），
 * 如果它们是不同关系 OID（表示它们位于不同模式中）的话，它们不会冲突。
 */
void checkNameSpaceConflicts(ParseState* pstate, List* namespace1, List* namespace2)
{
    ListCell* l1 = NULL;

    // 遍历第一个命名空间列表
    foreach (l1, namespace1) {
        ParseNamespaceItem *nsitem1 = (ParseNamespaceItem *) lfirst(l1);
        RangeTblEntry *rte1 = nsitem1->p_rte;
        const char* aliasname1 = rte1->eref->aliasname;
        ListCell* l2 = NULL;

        // 遍历第二个命名空间列表
        foreach (l2, namespace2) {
            ParseNamespaceItem *nsitem2 = (ParseNamespaceItem *) lfirst(l2);
            RangeTblEntry *rte2 = nsitem2->p_rte;

            // 检查别名是否匹配
            if (strcmp(rte2->eref->aliasname, aliasname1) != 0) {
                continue; /* 绝对没有冲突 */
            }

            // 根据 SQL92 规则检查是否有冲突
            if (rte1->rtekind == RTE_RELATION && rte1->alias == NULL && rte2->rtekind == RTE_RELATION &&
                rte2->alias == NULL && rte1->relid != rte2->relid) {
                continue; /* 根据 SQL92 规则没有冲突 */
            }

            // 如果存在冲突，通过 ereport 抛出错误，指明表名重复
            ereport(ERROR,
                (errcode(ERRCODE_DUPLICATE_ALIAS), errmsg("table name \"%s\" specified more than once", aliasname1)));
        }
    }
}

/*
 * 给定一个 RTE，返回该条目的 RT 索引（从 1 开始），
 * 并可选择地获取其嵌套深度（0 = 当前层级）。
 * 如果 sublevels_up 为 NULL，则仅考虑当前嵌套层次的关系。
 * 如果未找到 RTE，将引发错误。
 */
int RTERangeTablePosn(ParseState* pstate, RangeTblEntry* rte, int* sublevels_up)
{
    int index;
    ListCell* l = NULL;

    if (sublevels_up != NULL) {
        *sublevels_up = 0;
    }

    while (pstate != NULL) {
        index = 1;
        foreach (l, pstate->p_rtable) {
            if (rte == (RangeTblEntry*)lfirst(l)) {
                return index;
            }
            index++;
        }
        pstate = pstate->parentParseState;
        if (sublevels_up != NULL) {
            (*sublevels_up)++;
        } else {
            break;
        }
    }

    // 如果未找到 RTE，引发错误
    ereport(ERROR, (errcode(ERRCODE_SYNTAX_ERROR), errmsg("RTE not found (internal error)")));
    return 0; /* 保持编译器安静 */
}

/*
 * 给定 RT 索引和嵌套深度，找到相应的 RTE。
 * 这是 RTERangeTablePosn 的逆操作。
 */
RangeTblEntry* GetRTEByRangeTablePosn(ParseState* pstate, int varno, int sublevels_up)
{
    while (sublevels_up-- > 0) {
        pstate = pstate->parentParseState;
        AssertEreport(pstate != NULL, MOD_OPT, "");
    }
    AssertEreport(varno > 0 && varno <= list_length(pstate->p_rtable), MOD_OPT, "");
    return rt_fetch(varno, pstate->p_rtable);
}

/*
 * 获取 CTE-reference RTE 的 CTE。
 *
 * rtelevelsup 是 RTE 来自给定 pstate 之上的查询层级数。
 * 如果调用者没有轻松获取此信息，可以传递 -1。
 */
CommonTableExpr* GetCTEForRTE(ParseState* pstate, RangeTblEntry* rte, int rtelevelsup)
{
    Index levelsup;
    ListCell* lc = NULL;

    /* 如果调用者不知道 rtelevelsup，则确定 RTE 的层级 */
    if (rtelevelsup < 0) {
        (void)RTERangeTablePosn(pstate, rte, &rtelevelsup);
    }

    AssertEreport(rte->rtekind == RTE_CTE, MOD_OPT, "");
    levelsup = rte->ctelevelsup + rtelevelsup;
    while (levelsup-- > 0) {
        pstate = pstate->parentParseState;
        if (pstate == NULL) /* 不应该发生 */
            ereport(ERROR,
                (errcode(ERRCODE_OPTIMIZER_INCONSISTENT_STATE), errmsg("bad levelsup for CTE \"%s\"", rte->ctename)));
    }
    foreach (lc, pstate->p_ctenamespace) {
        CommonTableExpr* cte = (CommonTableExpr*)lfirst(lc);

        if (strcmp(cte->ctename, rte->ctename) == 0) {
            return cte;
        }
    }
    /* 不应该发生 */
    ereport(ERROR, (errcode(ERRCODE_NO_DATA_FOUND), errmsg("could not find CTE \"%s\"", rte->ctename)));
    return NULL; /* 保持编译器安静 */
}
/*
 * scanRTEForColumn
 *	  在单个RangeTblEntry（RTE）的列名（或别名）中搜索指定的列名。如果找到，
 *	  则返回相应的Var节点；否则返回NULL。如果在此RTE内的名称模糊，引发错误。
 *	  如果omit_excluded为true，则排除标记为排除的隐藏列。
 *
 *	  副作用：如果找到匹配项，则将RTE标记为需要对该列进行读取访问。
 *
 * 参数：
 *	- pstate: 代表当前解析状态的ParseState
 *	- rte: 要搜索的RangeTblEntry
 *	- colname: 要搜索的列名
 *	- location: 列名在SQL语句中的位置
 *	- omit_excluded: 是否排除隐藏的被标记为排除的列
 *
 * 返回值：
 *	- 如果找到匹配项，返回相应的Var节点；否则返回NULL。
 *
 * 注意：
 *	- 这个函数搜索RTE的用户列名（或别名），如果有多个匹配项则报错。
 *	- 如果RTE表示真实表，还考虑系统列名。
 *	- 如果pstate的p_expr_kind是EXPR_KIND_GENERATED_COLUMN，则不允许使用系统列。
 *	- 如果找到匹配项，将返回一个Var节点，并标记RTE需要读取访问该列。
 *	- 如果未找到匹配项，则返回NULL。
 */
Node* scanRTEForColumn(ParseState* pstate, RangeTblEntry* rte, char* colname, int location, bool omit_excluded)
{
    Node* result = NULL;
    int attnum = 0;
    Var* var = NULL;
    ListCell* c = NULL;

    /*
     * 遍历用户列名（或别名）以查找匹配项。如果有多个匹配项，则报错。
     * 注意：eref->colnames可能包含已删除列的条目，但这些将是空字符串，不能匹配任何合法的SQL标识符，因此我们不在这里进行测试。
     * 如果出现访问已删除的列的情况，我们仍将通过get_rte_attribute_type()的检查捕获到，该函数由make_var()调用。该函数必须进行缓存查找，因此该检查是便宜的。
     */
    foreach (c, rte->eref->colnames) {
        attnum++;
        if (omit_excluded && rte->isexcluded) {
            continue;
        }
        if (strcmp(strVal(lfirst(c)), colname) == 0) {
            if (result != NULL) {
                ereport(ERROR,
                    (errcode(ERRCODE_AMBIGUOUS_COLUMN),
                        errmsg("column reference \"%s\" is ambiguous", colname),
                        parser_errposition(pstate, location)));
            }

            /*
             * 当用户指定查询隐藏列时，但它实际上对用户不可见时。
             * 因此只需忽略此列，这仅发生在时序表上。
             */
            if (strcmp(TS_PSEUDO_DIST_COLUMN, colname) == 0) {
                var = ts_make_var(pstate, rte, attnum, location);
                if (var == NULL) {
                    continue;
                }
            } else {
                var = make_var(pstate, rte, attnum, location);
            }
            /* 需要对列进行读取访问 */
            markVarForSelectPriv(pstate, var, rte);
            result = (Node*)var;
        }
    }

    /*
     * 如果有唯一匹配项，返回它。注意，这允许用户别名覆盖系统列名（如OID）而不引发错误。
     */
    if (result != NULL) {
        return result;
    }

    /*
     * 如果RTE表示真实表，考虑系统列名。
     */
    if (rte->rtekind == RTE_RELATION && rte->relkind != RELKIND_FOREIGN_TABLE && rte->relkind != RELKIND_STREAM) {
        /* 快速检查名称是否可能是系统列 */
        attnum = specialAttNum(colname);

        /*
         * 在生成的列中，不允许使用系统列，除了tableOid。
         */
        if (pstate->p_expr_kind == EXPR_KIND_GENERATED_COLUMN && attnum < InvalidAttrNumber) {
            ereport(ERROR,
                (errmodule(MOD_GEN_COL),
                    errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
                    errmsg("cannot use system column \"%s\" in column generation expression", colname),
                    parser_errposition(pstate, location)));
        }
        if (attnum != InvalidAttrNumber) {
            /*
             * 现在检查列是否实际已定义。由于DefineQueryRewrite的一个古老疏忽，有可能pg_attribute包含视图的系统列的条目，
             * 即使视图不应该有这样的条目 --- 因此我们还检查relkind。这种刻意的假设在9.3版本及以后的版本中将不再需要。
             */
            if (SearchSysCacheExists2(ATTNUM, ObjectIdGetDatum(rte->relid), Int16GetDatum(attnum)) &&
                get_rel_relkind(rte->relid) != RELKIND_VIEW && get_rel_relkind(rte->relid) != RELKIND_CONTQUERY) {
                var = make_var(pstate, rte, attnum, location);
                /* 需要对列进行读取访问 */
                markVarForSelectPriv(pstate, var, rte);
                result = (Node*)var;
            }
        }
    }

    return result;
}

/*
 * colNameToVar
 *	  搜索未限定的列名。如果找到，返回相应的Var节点（或表达式）；如果找不到，则返回NULL。
 *	  如果名称在当前查询中模糊，引发错误。如果localonly为true，则仅考虑最内层查询中的名称。
 *
 * 参数：
 *	- pstate: 代表当前解析状态的ParseState
 *	- colname: 要搜索的列名
 *	- localonly: 是否仅考虑最内层查询中的名称
 *	- location: 列名在SQL语句中的位置
 *	- final_rte: 输出参数，用于存储找到的RTE（如果找到）
 *
 * 返回值：
 *	- 如果找到匹配项，返回相应的Var节点（或表达式）；如果找不到，则返回NULL。
 *
 * 注意：
 *	- 本函数在pstate的p_varnamespace中查找列名。
 *	- 如果找到匹配项，将返回Var节点，并将找到的RTE存储在final_rte中。
 *	- 如果找不到匹配项，则返回NULL。
 *	- 如果列名模糊，引发错误。
 *	- 如果localonly为true，则仅在最内层查询中查找。
 */
Node* colNameToVar(ParseState* pstate, char* colname, bool localonly, int location, RangeTblEntry** final_rte)
{
    Node* result = NULL;
    ParseState* orig_pstate = pstate;

    while (pstate != NULL) {
        ListCell* l = NULL;

        foreach (l, pstate->p_varnamespace) {
            ParseNamespaceItem *nsitem = (ParseNamespaceItem *) lfirst(l);
            RangeTblEntry *rte = nsitem->p_rte;
            Node* newresult = NULL;

            /* 如果不在LATERAL中，则忽略仅LATERAL的条目 */
            if (nsitem->p_lateral_only && !pstate->p_lateral_active)
                continue;

            /* 使用orig_pstate以获取正确的sublevels_up */
            newresult = scanRTEForColumn(orig_pstate, rte, colname, location, true);

            if (newresult != NULL) {
                if (final_rte != NULL) {
                    *final_rte = rte;
                }

                /*
                 * 在正常情况下，同名的用户别名需要指定，但在某些情况下，可能无法指定。
                 * 例如，在'merge into (matched)'场景下，优先在目标RTE中查找。如果找到，则跳出循环。否则在源RTE中查找。
                 * 这个搜索顺序也在RTE列表的顺序中找到，pstate的use_level属性表示是否使用此规则。
                 */
                if (result != NULL && pstate->use_level) {
                    break;
                }

                if (result != NULL) {
                    ereport(ERROR,
                        (errcode(ERRCODE_AMBIGUOUS_COLUMN),
                            errmsg("column reference \"%s\" is ambiguous", colname),
                            parser_errposition(orig_pstate, location)));
				}
                /* SQL:2008要求这是一个错误，而不是不可见的项目 */
                if (nsitem->p_lateral_only && !nsitem->p_lateral_ok)
                    ereport(ERROR,
                            (errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
                            errmsg("invalid reference to FROM-clause entry for table \"%s\"", rte->eref->aliasname),
                            errdetail("The combining JOIN type must be INNER or LEFT for a LATERAL reference."),
                            parser_errposition(orig_pstate, location)));
                result = newresult;
            }
        }

        if (result != NULL || localonly) {
            break; /* 找到，或者不想查看父级 */
        }

        pstate = pstate->parentParseState;
    }

    return result;
}

/*
 * searchRangeTableForCol
 *   在查询的所有RangeTblEntry中搜索是否存在可以提供给定列名的数据表。
 *   如果找到，返回对应的RangeTblEntry；否则，返回NULL。
 *
 *   该函数在整个查询范围内搜索，不仅考虑当前可见的p_varnamespace列表，
 *   这个行为在SQL规范中是无效的，可能会导致模棱两可的结果，
 *   因此只应作为在适当时候生成合适的错误消息的启发式方法来使用。
 *   具体用法见errorMissingColumn。
 */
static RangeTblEntry *
searchRangeTableForCol(ParseState *pstate, char *colname, int location)
{
    ParseState *orig_pstate = pstate;

    while (pstate != NULL)
    {
        ListCell   *l = NULL;

        foreach(l, pstate->p_rtable)
        {
            RangeTblEntry *rte = (RangeTblEntry *)lfirst(l);
            if (scanRTEForColumn(orig_pstate, rte, colname, location))
                return rte;
        }
        pstate = pstate->parentParseState;
    }
    return NULL;
}

/*
 * markRTEForSelectPriv
 *   标记RTE的指定列为需要SELECT权限。
 *
 *   如果col为InvalidAttrNumber，则表示整个行引用。
 *   调用者应传递实际的RTE，如果手头有的话；否则传递NULL，
 *   我们将在此查找。
 */
static void markRTEForSelectPriv(ParseState* pstate, RangeTblEntry* rte, int rtindex, AttrNumber col)
{
    if (rte == NULL) {
        rte = rt_fetch(rtindex, pstate->p_rtable);
    }

    if (rte->rtekind == RTE_RELATION) {
        /* 确保整个rel被标记为SELECT权限 */
        rte->requiredPerms |= ACL_SELECT;
        /* 必须偏移attnum以适应bitmapset */
        rte->selectedCols = bms_add_member(rte->selectedCols, col - FirstLowInvalidHeapAttributeNumber);
    } else if (rte->rtekind == RTE_JOIN) {
        if (col == InvalidAttrNumber) {
            /* 对JOIN的整行引用需要对两个输入进行相应处理 */
            JoinExpr* j = NULL;

            if (rtindex > 0 && rtindex <= list_length(pstate->p_joinexprs)) {
                j = (JoinExpr*)list_nth(pstate->p_joinexprs, rtindex - 1);
            } else {
                j = NULL;
            }
            if (j == NULL) {
                ereport(
                    ERROR, (errcode(ERRCODE_NO_DATA_FOUND), errmsg("could not find JoinExpr for whole-row reference")));
            }
            AssertEreport(IsA(j, JoinExpr), MOD_OPT, "");

            if (IsA(j->larg, RangeTblRef)) {
                int varno = ((RangeTblRef*)j->larg)->rtindex;
                markRTEForSelectPriv(pstate, NULL, varno, InvalidAttrNumber);
            } else if (IsA(j->larg, JoinExpr)) {
                int varno = ((JoinExpr*)j->larg)->rtindex;
                markRTEForSelectPriv(pstate, NULL, varno, InvalidAttrNumber);
            } else {
                ereport(ERROR,
                    (errcode(ERRCODE_UNRECOGNIZED_NODE_TYPE),
                        errmsg("unrecognized node type: %d", (int)nodeTag(j->rarg))));
            }

            if (IsA(j->rarg, RangeTblRef)) {
                int varno = ((RangeTblRef*)j->rarg)->rtindex;
                markRTEForSelectPriv(pstate, NULL, varno, InvalidAttrNumber);
            } else if (IsA(j->rarg, JoinExpr)) {
                int varno = ((JoinExpr*)j->rarg)->rtindex;
                markRTEForSelectPriv(pstate, NULL, varno, InvalidAttrNumber);
            } else {
                ereport(ERROR,
                    (errcode(ERRCODE_UNRECOGNIZED_NODE_TYPE),
                        errmsg("unrecognized node type: %d", (int)nodeTag(j->rarg))));
            }
        } else {
            /* 对于常规的JOIN属性，查看别名-变量列表 */
            Var* aliasvar = NULL;
            AssertEreport(col > 0 && col <= list_length(rte->joinaliasvars), MOD_OPT, "");
            aliasvar = (Var*)list_nth(rte->joinaliasvars, col - 1);

            if (IsA(aliasvar, Var)) {
                markVarForSelectPriv(pstate, aliasvar, NULL);
            }
        }
    }
    /* 其他RTE类型不需要权限标记 */
}

/*
 * markVarForSelectPriv
 *   标记由Var引用的RTE为需要SELECT权限。
 *
 *   调用者应传递Var的引用RTE，如果手头有的话（几乎所有都有）；
 *   否则传递NULL。
 */
void markVarForSelectPriv(ParseState* pstate, Var* var, RangeTblEntry* rte)
{
    Index lv;

    AssertEreport(IsA(var, Var), MOD_OPT, "");
    /* 如果是上层Var，找到适当的pstate */
    for (lv = 0; lv < var->varlevelsup; lv++) {
        pstate = pstate->parentParseState;
    }
    markRTEForSelectPriv(pstate, rte, var->varno, var->varattno);
}


/*
 * buildRelationAliases
 * 构建关系 RTE 的 eref 列名列表。这个函数还用于处理函数 RTE 返回具名复合类型的情况。
 *
 * 参数：
 * tupdesc: 物理列信息（TupleDesc）
 * alias: 用户提供的别名，如果没有则为 NULL
 * eref: 用于存储列名列表的 eref Alias 结构
 *
 * eref->colnames 被填充。同时，alias->colnames 被重建以插入任何已删除列的空字符串，以便与物理列的编号一一对应。
 */
static void buildRelationAliases(TupleDesc tupdesc, Alias* alias, Alias* eref)
{
    int maxattrs = tupdesc->natts;  // 获取列的数量
    ListCell* aliaslc = NULL;
    int numaliases;
    int varattno;
    int numdropped = 0;

    AssertEreport(eref->colnames == NIL, MOD_OPT, "");

    if (alias != NULL) {
        aliaslc = list_head(alias->colnames);
        numaliases = list_length(alias->colnames);
        alias->colnames = NIL;  // 重建别名列表
    } else {
        aliaslc = NULL;
        numaliases = 0;
    }

    // 遍历物理列
    for (varattno = 0; varattno < maxattrs; varattno++) {
        Form_pg_attribute attr = &tupdesc->attrs[varattno];
        Value* attrname = NULL;

        if (attr->attisdropped) {
            // 对于已删除的列，插入空字符串
            attrname = makeString(pstrdup(""));
            if (aliaslc != NULL) {
                alias->colnames = lappend(alias->colnames, attrname);
            }
            numdropped++;
        } else if (aliaslc != NULL) {
            // 使用下一个用户提供的别名
            attrname = (Value*)lfirst(aliaslc);
            aliaslc = lnext(aliaslc);
            alias->colnames = lappend(alias->colnames, attrname);
        } else {
            // 否则使用列的实际名称
            attrname = makeString(pstrdup(NameStr(attr->attname)));
        }

        eref->colnames = lappend(eref->colnames, attrname);
    }

    // 检查是否存在过多的用户提供的别名
    if (aliaslc != NULL) {
        ereport(ERROR,
            (errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
                errmsg("table \"%s\" has %d columns available but %d columns specified",
                    eref->aliasname,
                    maxattrs - numdropped,
                    numaliases)));
    }
}

/*
 * buildScalarFunctionAlias
 * 为返回标量类型的函数 RTE 构建 eref 列名列表。
 *
 * 参数：
 * funcexpr: 函数调用的转换后的表达式树
 * funcname: 函数名（仅用于错误消息）
 * alias: 用户提供的别名，如果没有则为 NULL
 * eref: 用于存储列名列表的 eref Alias 结构
 *
 * eref->colnames 被填充。
 */
static void buildScalarFunctionAlias(Node* funcexpr, char* funcname, Alias* alias, Alias* eref)
{
    char* pname = NULL;

    AssertEreport(eref->colnames == NIL, MOD_OPT, "");

    // 如果用户提供了别名并且有且只有一个，使用用户提供的别名
    if (alias != NULL && alias->colnames != NIL) {
        if (list_length(alias->colnames) != 1) {
            ereport(ERROR,
                (errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
                    errmsg("too many column aliases specified for function %s", funcname)));
        }
        eref->colnames = (List*)copyObject(alias->colnames);
        return;
    }

    // 如果函数调用是一个简单的函数，并且该函数具有单个已命名的 OUT 参数，使用该参数的名称
    if (funcexpr && IsA(funcexpr, FuncExpr)) {
        pname = get_func_result_name(((FuncExpr*)funcexpr)->funcid);
        if (pname != NULL) {
            eref->colnames = list_make1(makeString(pname));
            return;
        }
    }

    // 否则使用之前确定的别名（不一定是函数名！）
    eref->colnames = list_make1(makeString(eref->aliasname));
}

/*
 * CopyAttributeInfo
 *   复制源表的属性信息到目标表的属性信息
 */
static void CopyAttributeInfo(Form_pg_attribute newtuple, Form_pg_attribute oldtuple)
{
    newtuple->attnum = oldtuple->attnum;
    newtuple->atttypid = oldtuple->atttypid;
    newtuple->attlen = oldtuple->attlen;
    newtuple->atttypmod = oldtuple->atttypmod;
    // 用于物化视图
    newtuple->attcollation = oldtuple->attcollation;
    newtuple->attbyval = oldtuple->attbyval;
    newtuple->attstorage = oldtuple->attstorage;
}

/*
 * CheckViewColumnExists
 *   检查视图中是否存在指定列，存在则获取列的属性信息
 */
static void CheckViewColumnExists(Oid view_oid, int2 attnum, Form_pg_attribute newtuple)
{
    HeapTuple tuple;
    Form_pg_attribute form_attribute;
    
    // 通过属性号和关系oid搜索系统缓存获取属性元组
    tuple = SearchSysCache2(ATTNUM, ObjectIdGetDatum(view_oid), Int16GetDatum(attnum));
    if (!HeapTupleIsValid(tuple)) {
        elog(ERROR, "catalog lookup failed for column %d of relation %u", attnum, view_oid);
    }
    
    form_attribute = (Form_pg_attribute)GETSTRUCT(tuple);
    CopyAttributeInfo(newtuple, form_attribute);
    ReleaseSysCache(tuple);
}

/*
 * CheckRelationColumnExists
 *   检查关系中是否存在指定列，存在则获取列的属性信息
 */
static bool CheckRelationColumnExists(Oid rel_oid, int2 attnum, Form_pg_attribute attrtuple)
{
    HeapTuple tuple;
    Form_pg_attribute attForm;
    
    // 通过属性号和关系oid搜索系统缓存获取属性元组
    tuple = SearchSysCache2(ATTNUM, ObjectIdGetDatum(rel_oid), Int16GetDatum(attnum));
    if (!HeapTupleIsValid(tuple)) {
        elog(ERROR, "catalog lookup failed for column %d of relation %u", attnum, rel_oid);
    }
    
    attForm = (Form_pg_attribute)GETSTRUCT(tuple);
    
    if (!attForm->attisdropped) {
        CopyAttributeInfo(attrtuple, attForm);
        ReleaseSysCache(tuple);
        return true;
    }
    
    // 对于被删除的列，需要通过被删除列名重新搜索系统缓存获取属性元组
    const char* droppedname = attForm->attdroppedname.data;
    HeapTuple tuple_drop;
    Form_pg_attribute attForm_drop;
    
    tuple_drop = SearchSysCache2(ATTNAME, ObjectIdGetDatum(rel_oid), CStringGetDatum(droppedname));
    ReleaseSysCache(tuple);
    
    if (!HeapTupleIsValid(tuple_drop)) {
        return false;
    }
    
    attForm_drop = (Form_pg_attribute)GETSTRUCT(tuple_drop);
    CopyAttributeInfo(attrtuple, attForm_drop);
    ReleaseSysCache(tuple_drop);
    return true;
}

/*
 * CheckPgAttribute
 *   检查系统表 pg_attribute 中是否存在指定对象的列，存在则更新列的属性信息
 */
static void CheckPgAttribute(Oid obj_oid, char* attName, Form_pg_attribute new_attribute)
{
    const int keyNum = 2;
    Relation rel;
    ScanKeyData key[keyNum];
    SysScanDesc scan;
    HeapTuple tuple;
    HeapTuple new_dep_tuple;
    Form_pg_attribute attForm;
    
    // 打开 pg_attribute 表进行独占锁扫描
    rel = heap_open(AttributeRelationId, RowExclusiveLock);
    
    // 使用关系oid和属性名作为搜索键初始化扫描键
    ScanKeyInit(&key[0], Anum_pg_attribute_attrelid, BTEqualStrategyNumber, F_OIDEQ, ObjectIdGetDatum(obj_oid));
    ScanKeyInit(&key[1], Anum_pg_attribute_attname, BTEqualStrategyNumber, F_NAMEEQ, NameGetDatum(attName));
    
    // 开始系统表扫描
    scan = systable_beginscan(rel, AttributeRelidNameIndexId, true, SnapshotSelf, keyNum, &key[0]);
    tuple = systable_getnext(scan);
    
    // 未找到匹配的列，抛出错误
    if (!HeapTupleIsValid(tuple)) {
        systable_endscan(scan);
        heap_close(rel, RowExclusiveLock);
        elog(ERROR, "catalog lookup failed for column %s of relation %u", attName, obj_oid);
    }
    
    // 获取属性元组
    attForm = (Form_pg_attribute)GETSTRUCT(tuple);
    
    // 构造新的属性元组数据
    Datum values[Natts_pg_attribute] = { 0 };
    bool nulls[Natts_pg_attribute] = { 0 };
    bool replaces[Natts_pg_attribute] = { 0 };
    values[Anum_pg_attribute_atttypid - 1] = ObjectIdGetDatum(new_attribute->atttypid);
    values[Anum_pg_attribute_attlen - 1] = Int16GetDatum(new_attribute->attlen);
    values[Anum_pg_attribute_atttypmod - 1] = Int32GetDatum(new_attribute->atttypmod);
    values[Anum_pg_attribute_attbyval - 1] = BoolGetDatum(new_attribute->attbyval);
    values[Anum_pg_attribute_attstorage - 1] = CharGetDatum(new_attribute->attstorage);
    values[Anum_pg_attribute_attcollation - 1] = ObjectIdGetDatum(new_attribute->attcollation);
    replaces[Anum_pg_attribute_atttypid - 1] = true;
    replaces[Anum_pg_attribute_attlen - 1] = true;
    replaces[Anum_pg_attribute_atttypmod - 1] = true;
    replaces[Anum_pg_attribute_attbyval - 1] = true;
    replaces[Anum_pg_attribute_attstorage - 1] = true;
    replaces[Anum_pg_attribute_attcollation - 1] = true;
    
    // 修改并更新元组
    new_dep_tuple = heap_modify_tuple(tuple, RelationGetDescr(rel), values, nulls, replaces);
    simple_heap_update(rel, &new_dep_tuple->t_self, new_dep_tuple);
    CatalogUpdateIndexes(rel, new_dep_tuple);
    heap_freetuple_ext(new_dep_tuple);
    
    // 增加命令计数器，提交更新
    CommandCounterIncrement();
    
    // 结束系统表扫描
    systable_endscan(scan);
    
    // 关闭 pg_attribute 表
    heap_close(rel, RowExclusiveLock);
}

/*
 * ValidateDependView
 *    验证视图的有效性，并在需要时进行修复。
 *
 * 参数：
 *    view_oid - 视图的对象标识符
 *    objType  - 视图对象的类型，例如 OBJECT_TYPE_VIEW 或 OBJECT_TYPE_MATVIEW
 *
 * 返回值：
 *    如果视图有效或已成功修复，则返回 true，否则返回 false。
 */
bool ValidateDependView(Oid view_oid, char objType)
{
    bool isValid = true;
    Oid rw_objid = InvalidOid;

    // 1. 过滤出有效的视图
    if (GetPgObjectValid(view_oid, objType)) {
        return isValid;
    }

    // 2. 查找该视图在内部依赖的 pg_rewrite 条目
    const int keyNum = 2;
    ScanKeyData key[keyNum];
    SysScanDesc scan = NULL;
    HeapTuple tup = NULL;
    Relation rel = heap_open(DependRelationId, AccessShareLock);

    // 设置扫描键
    ScanKeyInit(&key[0], Anum_pg_depend_refclassid, BTEqualStrategyNumber, F_OIDEQ,
                ObjectIdGetDatum(RelationRelationId));
    ScanKeyInit(&key[1], Anum_pg_depend_refobjid, BTEqualStrategyNumber, F_OIDEQ, ObjectIdGetDatum(view_oid));
    scan = systable_beginscan(rel, DependReferenceIndexId, true, NULL, keyNum, key);

    // 遍历 pg_depend 表，查找 pg_rewrite 条目
    while (HeapTupleIsValid((tup = systable_getnext(scan)))) {
        Form_pg_depend depform = (Form_pg_depend)GETSTRUCT(tup);

        if (depform->classid == RewriteRelationId && depform->deptype == DEPENDENCY_INTERNAL) {
            rw_objid = depform->objid;
            break;
        }
    }

    systable_endscan(scan);
    heap_close(rel, AccessShareLock);

    // 未找到 pg_rewrite 条目，报错
    if (!OidIsValid(rw_objid)) {
        elog(ERROR, "cannot find the internal dependent pg_rewrite entry.");
    }

    // 3. 查找直接依赖的所有父视图和表的列，递归检查它们的有效性
    List *query_str = NIL;
    ScanKeyData key_dep[keyNum];
    SysScanDesc scan_dep = NULL;
    HeapTuple tup_dep = NULL;
    Relation rel_dep = heap_open(DependRelationId, RowExclusiveLock);
    ScanKeyInit(&key_dep[0], Anum_pg_depend_classid, BTEqualStrategyNumber, F_OIDEQ,
        ObjectIdGetDatum(RewriteRelationId));
    ScanKeyInit(&key_dep[1], Anum_pg_depend_objid, BTEqualStrategyNumber, F_OIDEQ, ObjectIdGetDatum(rw_objid));
    scan_dep = systable_beginscan(rel_dep, DependDependerIndexId, true, NULL, keyNum, key_dep);

    Form_pg_attribute newtuple = (Form_pg_attribute)palloc0(sizeof(FormData_pg_attribute));

    while (HeapTupleIsValid((tup_dep = systable_getnext(scan_dep)))) {
        Form_pg_depend depform = (Form_pg_depend)GETSTRUCT(tup_dep);

        if (depform->refclassid != RelationRelationId || depform->deptype != DEPENDENCY_NORMAL ||
            depform->refobjsubid == 0) {
            continue;
        }

        Oid dep_objid = depform->refobjid;
        int2 dep_objsubid = depform->refobjsubid;
        char relkind = get_rel_relkind(dep_objid);
        char* attName = NULL;

        if (relkind == RELKIND_RELATION) {
            // 列存在，检查其类型是否发生变化或是否已被删除并重新创建
            isValid &= CheckRelationColumnExists(dep_objid, dep_objsubid, newtuple);

            if (newtuple->attnum > 0) {
                // 修改 pg_depend 表
                Datum values[Natts_pg_depend] = { 0 };
                bool nulls[Natts_pg_depend] = { 0 };
                bool replaces[Natts_pg_depend] = { 0 };
                HeapTuple new_dep_tuple;

                values[Anum_pg_depend_refobjsubid - 1] = Int32GetDatum(newtuple->attnum);
                replaces[Anum_pg_depend_refobjsubid - 1] = true;

                new_dep_tuple = heap_modify_tuple(tup_dep, RelationGetDescr(rel_dep), values, nulls, replaces);
                simple_heap_update(rel_dep, &new_dep_tuple->t_self, new_dep_tuple);
                CatalogUpdateIndexes(rel_dep, new_dep_tuple);
                heap_freetuple_ext(new_dep_tuple);
                CommandCounterIncrement();

                // 修改 pg_rewrite 的 targetEntry
                CheckPgRewriteWithDroppedColumn(dep_objid, rw_objid, newtuple, dep_objsubid, &attName, &query_str);

                // 修改 pg_attribute
                CheckPgAttribute(view_oid, attName, newtuple);
            }
        } else if (relkind == RELKIND_VIEW || relkind == RELKIND_MATVIEW) {
            isValid &= ValidateDependView(dep_objid,
                                          relkind == RELKIND_VIEW ? OBJECT_TYPE_VIEW : OBJECT_TYPE_MATVIEW);

            if (isValid) {
                // 说明 dep_objid 有效，应保持 view_oid.attr 与 dep_objid.dep_objsubid 相同
                // 查找 dep_objid.dep_objsubid
                CheckViewColumnExists(dep_objid, dep_objsubid, newtuple);

                // 修改 pg_rewrite 的 targetEntry
                CheckPgRewriteWithDroppedColumn(dep_objid, rw_objid, newtuple, dep_objsubid, &attName, &query_str);

                // 修改 pg_attribute
                CheckPgAttribute(view_oid, attName, newtuple);
            }
        }

        // 重置 newtuple 的内存
        errno_t rc = memset_s(newtuple, sizeof(FormData_pg_attribute), 0, sizeof(FormData_pg_attribute));
        securec_check_c(rc, "\0", "\0");

        pfree_ext(attName);

        // 如果不再有效，释放内存并返回 false
        if (!isValid) {
            pfree_ext(newtuple);
            systable_endscan(scan_dep);
            heap_close(rel_dep, RowExclusiveLock);
            return false;
        }
    }

    pfree_ext(newtuple);
    systable_endscan(scan_dep);
    heap_close(rel_dep, RowExclusiveLock);

    // 4. 标记当前视图为有效
    SetPgObjectValid(view_oid, objType, true);

    // 对于 OBJECT_TYPE_VIEW，执行 Create or Replace View 查询
    if (objType == OBJECT_TYPE_VIEW) {
        ReplaceViewQueryFirstAfter(query_str);
        CommandCounterIncrement();
    }

    return isValid;
}


/*
 * 在解析分析期间打开一个表
 *
 * 这本质上与heap_openrv()相同，不同之处在于它满足一些特定于解析器的错误报告需求，特别是它安排包含RangeVar的解析位置的任何生成错误。
 *
 * 注意：正确的做法是lockmode应该声明为LOCKMODE而不是int，但那需要在parse_relation.h中导入storage/lock/lock.h。
 * 由于LOCKMODE已经被typedef为int，这似乎有点过度。
 */
Relation parserOpenTable(ParseState *pstate, const RangeVar *relation, int lockmode, bool isFirstNode,
                         bool isCreateView, bool isSupportSynonym)
{
    Relation rel = NULL;
    ParseCallbackState pcbstate;
    StringInfoData detailInfo;
    initStringInfo(&detailInfo);

    char *snapshot_name = strchr(relation->relname, DB4AI_SNAPSHOT_VERSION_DELIMITER);
    if (unlikely(snapshot_name)) {
        *snapshot_name = *u_sess->attr.attr_sql.db4ai_snapshot_version_delimiter;
        while (*(++snapshot_name)) {
            if (*snapshot_name == DB4AI_SNAPSHOT_VERSION_SEPARATOR) {
                *snapshot_name = *u_sess->attr.attr_sql.db4ai_snapshot_version_separator;
            }
        }
    }

    setup_parser_errposition_callback(&pcbstate, pstate, relation->location);
    rel = HeapOpenrvExtended(relation, lockmode, true, isSupportSynonym, &detailInfo);
    if (rel == NULL) {
        /* 如果detailInfo有一些消息，报告一些错误和详细信息。 */
#ifdef ENABLE_MOT
        if (u_sess->mot_cxt.jit_compile_depth > 0) {
            u_sess->mot_cxt.jit_parse_error = MOT_JIT_TABLE_NOT_FOUND;
        }
#endif
        if (relation->schemaname) {
            if (IS_PGXC_DATANODE) {
                /*
                 * 支持多节点组，也许关系在协调器，
                 * 但在数据节点上不存在。
                 */
                if (detailInfo.len > 0) {
                    ereport(ERROR,
                        (errcode(ERRCODE_UNDEFINED_TABLE),
                            errmsg("relation \"%s.%s\" does not exist on%s %s",
                                relation->schemaname,
                                relation->relname,
                                (IS_SINGLE_NODE ? "" : " DN"),
                                g_instance.attr.attr_common.PGXCNodeName),
                            errdetail("%s", detailInfo.data)));
                } else {
                    ereport(ERROR,
                        (errcode(ERRCODE_UNDEFINED_TABLE),
                            errmsg("relation \"%s.%s\" does not exist on%s %s",
                                relation->schemaname,
                                relation->relname,
                                (IS_SINGLE_NODE ? "" : " DN"),
                                g_instance.attr.attr_common.PGXCNodeName)));
                }
            } else {
                if (detailInfo.len > 0) {
                    ereport(ERROR,
                        (errcode(ERRCODE_UNDEFINED_TABLE),
                            errmsg("relation \"%s.%s\" does not exist", relation->schemaname, relation->relname),
                            errdetail("%s", detailInfo.data)));
                } else {
                    ereport(ERROR,
                        (errcode(ERRCODE_UNDEFINED_TABLE),
                            errmsg("relation \"%s.%s\" does not exist", relation->schemaname, relation->relname)));
                }
            }
        } else {
            /*
             * 一个未限定的名称可能被认为是对尚未在作用域内的CTE的引用。
             * 对于解决这些问题，裸体的“不存在”消息已经被证明是非常无用的，
             * 因此我们竭尽全力提供一个具体的提示。
             */
            if (isFutureCTE(pstate, relation->relname)) {
                ereport(ERROR,
                    (errcode(ERRCODE_UNDEFINED_TABLE),
                        errmsg("relation \"%s\" does not exist", relation->relname),
                        errdetail("There is a WITH item named \"%s\", but it cannot be referenced from this part of "
                                  "the query.",
                            relation->relname),
                        errhint("Use WITH RECURSIVE, or re-order the WITH items to remove forward references.")));
            } else {
                errno_t rc = 0;
                if (IS_PGXC_DATANODE) {
                    /*
                     * 支持多节点组，也许关系在协调器，
                     * 但在数据节点上不存在。
                     */
                    if (detailInfo.len > 0) {
                        char message[MAXSTRLEN];
                        rc = sprintf_s(message, MAXSTRLEN, "relation \"%s\" does not exist", relation->relname);
                        securec_check_ss_c(rc, "", "");
                        InsertErrorMessage(message, u_sess->plsql_cxt.plpgsql_yylloc, true);
                        ereport(ERROR,
                            (errcode(ERRCODE_UNDEFINED_TABLE),
                                errmsg("relation \"%s\" does not exist on%s %s",
                                    relation->relname,
                                    (IS_SINGLE_NODE ? "" : " DN"),
                                    g_instance.attr.attr_common.PGXCNodeName),
                                errdetail("%s", detailInfo.data)));
                    } else {
                        char message[MAXSTRLEN];
                        rc = sprintf_s(message, MAXSTRLEN, "relation \"%s\" does not exist", relation->relname);
                        securec_check_ss_c(rc, "", "");
                        InsertErrorMessage(message, u_sess->plsql_cxt.plpgsql_yylloc, true);
                        ereport(ERROR,
                            (errcode(ERRCODE_UNDEFINED_TABLE),
                                errmsg("relation \"%s\" does not exist on%s %s",
                                    relation->relname,
                                    (IS_SINGLE_NODE ? "" : " DN"),
                                    g_instance.attr.attr_common.PGXCNodeName)));
                    }
                } else {
                    char message[MAXSTRLEN];
                    rc = sprintf_s(message, MAXSTRLEN, "relation \"%s\" does not exist", relation->relname);
                    securec_check_ss_c(rc, "", "");
                    InsertErrorMessage(message, u_sess->plsql_cxt.plpgsql_yylloc, true);
                    if (detailInfo.len > 0) {
                        ereport(ERROR,
                            (errcode(ERRCODE_UNDEFINED_TABLE),
                                errmsg("relation \"%s\" does not exist", relation->relname),
                                errdetail("%s", detailInfo.data)));
                    } else {
                        char message[MAXSTRLEN];
                        rc = sprintf_s(message, MAXSTRLEN, "relation \"%s\" does not exist", relation->relname);
                        securec_check_ss_c(rc, "", "");
                        InsertErrorMessage(message, u_sess->plsql_cxt.plpgsql_yylloc, true);
                        ereport(ERROR,
                            (errcode(ERRCODE_UNDEFINED_TABLE),
                                errmsg("relation \"%s\" does not exist", relation->relname)));
                    }
                }
            }
        }
    }
    cancel_parser_errposition_callback(&pcbstate);

    /* 禁止在回收站对象上执行DQL/DML */
    TrForbidAccessRbObject(RelationRelationId, RelationGetRelid(rel), relation->relname);

    /* 检查wlm会话信息在此数据库中是否有效 */
    if (ENABLE_WORKLOAD_CONTROL && !CheckWLMSessionInfoTableValid(relation->relname) && !u_sess->attr.attr_common.IsInplaceUpgrade) {
        ereport(NOTICE,
            (errcode(ERRCODE_UNDEFINED_TABLE),
                errmsg("relation \"%s\" has data only in database \"postgres\"", relation->relname),
                errhint("please use database \"postgres\"")));
    }
    
    if (RelationGetRelkind(rel) == RELKIND_VIEW &&
        RelationGetRelid(rel) >= FirstNormalObjectId &&
        !ValidateDependView(RelationGetRelid(rel), OBJECT_TYPE_VIEW)) {
        ereport(ERROR,
            (errcode(ERRCODE_UNDEFINED_OBJECT),
                errmsg("The view %s is invalid, please make it valid before operation.",
                       RelationGetRelationName(rel)),
                    errhint("Please re-add missing table fields.")));
    }
    
    if (!u_sess->attr.attr_common.XactReadOnly && rel->rd_id == UserStatusRelationId) {
        TryUnlockAllAccounts();
    }

#ifndef ENABLE_MULTIPLE_NODES
    if (RelationIsPartitioned(rel)) {
        /* 采取ShareLock以避免PARTITION DDL COMMIT，直到我们完成InitPlan。分布模式不支持分区DDL/DML并行工作，因此不需要此操作 */
        LockPartitionObject(RelationGetRelid(rel), PARTITION_OBJECT_LOCK_SDEQUENCE, PARTITION_SHARE_LOCK);
        AddPartitionDMLInfo(RelationGetRelid(rel));
    }
#endif

    if (IS_PGXC_COORDINATOR && !IsConnFromCoord()) {
        if (u_sess->attr.attr_sql.enable_parallel_ddl && !isFirstNode && isCreateView) {
            UnlockRelation(rel, lockmode);
        }
    }

    return rel;
}

/*
 * 将一个关系添加到解析状态的范围表中
 *
 * 如果解析状态（pstate）为NULL，只是构建一个范围表条目（RTE），而不将其添加到范围表列表中。
 *
 * 注意：以前此函数检查了引用名称的冲突，但这是错误的。
 * 调用者负责在适当的范围内检查冲突。
 */
RangeTblEntry* addRangeTableEntry(ParseState* pstate, RangeVar* relation, Alias* alias, bool inh, bool inFromCl,
    bool isFirstNode, bool isCreateView, bool isSupportSynonym)
{
    RangeTblEntry* rte = makeNode(RangeTblEntry);
    char* refname = alias ? alias->aliasname : relation->relname;
    LOCKMODE lockmode;
    Relation rel;

    rte->rtekind = RTE_RELATION;
    rte->alias = alias;
    rte->isexcluded = false;

    if (pstate == NULL) {
        ereport(ERROR, (errmodule(MOD_OPT), errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED), errmsg("pstate 不能为空")));
    }

    /*
     * 获取关系的OID。此访问还确保我们对关系具有最新的relcache条目。
     * 由于这通常是语句中对关系的第一次访问，因此根据我们是否执行SELECT FOR UPDATE/SHARE，小心获取正确的访问级别。
     */
    lockmode = isLockedRefname(pstate, refname) ? RowShareLock : AccessShareLock;
    rel = parserOpenTable(pstate, relation, lockmode, isFirstNode, isCreateView, isSupportSynonym);
    if (relation->withVerExpr) {
        LOCKMODE lockmodePro = lockmode;
        tableam_tcap_promote_lock(rel, &lockmodePro);
        if (lockmodePro > lockmode) {
            LockRelationOid(RelationGetRelid(rel), lockmodePro);
        }
    }
    if (IS_FOREIGNTABLE(rel) || IS_STREAM_TABLE(rel)) {
        /*
         * 在安全模式下，在用户选择来自外部表的数据之前，必须检查用户是否具有useft权限。
         */
        if (isSecurityMode && !have_useft_privilege()) {
            ereport(ERROR,
                (errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
                    errmsg("在安全模式下，无权从外部表中选择")));
        }
    }

    rte->relid = RelationGetRelid(rel);
    rte->relkind = rel->rd_rel->relkind;

    rte->is_ustore = RelationIsUstoreFormat(rel);
    rte->ispartrel = RELATION_IS_PARTITIONED(rel);
    rte->relhasbucket = RELATION_HAS_BUCKET(rel);
    rte->bucketmapsize = rel->rd_bucketmapsize;
    /* 标记引用的同义词OID。*/
    rte->refSynOid = rel->rd_refSynOid;

    /* 选择子句包含分区。 */
    if (relation->ispartition) {
        rte->isContainPartition = GetPartitionOidForRTE(rte, relation, pstate, rel);
    }
    /* 选择子句包含子分区。 */
    if (relation->issubpartition) {
        rte->isContainSubPartition = GetSubPartitionOidForRTE(rte, relation, pstate, rel);
    }
    /* 删除子句包含PARTITION (..., ...)。 */
    if (list_length(relation->partitionNameList) > 0) {
        GetPartitionOidListForRTE(rte, relation);
    }
#ifdef ENABLE_MULTIPLE_NODES
    if (!rte->relhasbucket && relation->isbucket) {
        ereport(ERROR, (errmsg("表是普通的，不能包含桶(0,1,2...)")));
    }
    /* 选择子句包含bucketids。 */
    if (hasValidBuckets(relation, rel->rd_bucketmapsize)) {
        if (!(rte->relhasbucket)) {
            ereport(ERROR, (errmsg("关系 \"%s\" 没有哈希桶", refname)));
        }

        rte->isbucket = true;
        rte->buckets = RangeVarGetBucketList(relation);
    }
#endif

#ifdef PGXC
    rte->relname = pstrdup(RelationGetRelationName(rel));
    rte->partAttrNum = get_rte_part_attr_num(rel);
#endif

    /*
     * 使用用户提供的别名和/或实际列名构建有效列名列表。
     */
    rte->eref = makeAlias(refname, NIL);
    buildRelationAliases(rel->rd_att, alias, rte->eref);

    /*
     * 释放rel引用计数，但在事务结束之前保持访问锁，
     * 以便在我们完成之前不能删除表或修改其模式。
     */
    heap_close(rel, NoLock);

    /* 访问检查的初始默认值始终为CHECK-FOR-READ-access，
     * 这对于除了目标表以外的所有情况都是正确的。
     */
    set_rte_flags(rte, inh, inFromCl, ACL_SELECT);
    rte->lateral = false;

    setRteOrientation(rel, rte);

    /*
     * 将完成的RTE添加到pstate的范围表列表中，但不要添加到连接列表或命名空间中 - 调用者必须在适当的位置执行。
     */
    if (pstate != NULL) {
        pstate->p_rtable = lappend(pstate->p_rtable, rte);
        /*
         * 如果添加到p_rtable的rte由同义词对象引用，
         * 则标记pstate->p_hasSynonyms。
         */
        if (!pstate->p_hasSynonyms && OidIsValid(rte->refSynOid)) {
            pstate->p_hasSynonyms = true;
        }
    }

    /* B兼容性处理索引提示的预检查*/
    IndexHintType ihtype = INDEX_HINT_USE;
    if (DB_IS_CMPT(B_FORMAT) && relation->indexhints != NIL) {
        ihtype = preCheckIndexHints(pstate, relation->indexhints, rel);
        if (ihtype == INDEX_HINT_NOT_EXISTS) {
            ereport(ERROR,
            (errcode(ERRCODE_UNDEFINED_OBJECT),
                errmsg(
                    "在关系 %s 中不存在索引", RelationGetRelationName(rel))));
        } else if (ihtype == INDEX_HINT_MIX) {
            ereport(ERROR,
            (errcode(ERRCODE_DUPLICATE_OBJECT),
                errmsg("混合使用force index和use index")));
        }
    }
    return rte;
}

/*
 * 将一个关系添加到解析状态的范围表中
 *
 * 与addRangeTableEntry()相似，只是它基于已打开的关系而不是RangeVar引用创建RTE。
 */
RangeTblEntry* addRangeTableEntryForRelation(ParseState* pstate, Relation rel, Alias* alias, bool inh, bool inFromCl)
{
    RangeTblEntry* rte = makeNode(RangeTblEntry);
    char* refname = NULL;

    if (alias != NULL) {
        refname = alias->aliasname;
    } else if (OidIsValid(rel->rd_refSynOid)) {
        refname = GetQualifiedSynonymName(rel->rd_refSynOid, false);
    } else {
        refname = RelationGetRelationName(rel);
    }

    rte->rtekind = RTE_RELATION;
    rte->alias = alias;
    rte->relid = RelationGetRelid(rel);
    rte->relkind = rel->rd_rel->relkind;
    rte->is_ustore = RelationIsUstoreFormat(rel);
    rte->ispartrel = RELATION_IS_PARTITIONED(rel);
    rte->relhasbucket = RELATION_HAS_BUCKET(rel);
    rte->bucketmapsize = rel->rd_bucketmapsize;
    rte->isexcluded = false;
    /*
     * 在目标关系的rd_refSynOid有效的情况下，它已被一个同义词引用。
     * 因此，别名名称用于将其原始关系名称带走，以形成refname。
     */
    rte->refSynOid = rel->rd_refSynOid;

#ifdef PGXC
    rte->relname = pstrdup(RelationGetRelationName(rel));
    rte->partAttrNum = get_rte_part_attr_num(rel);
#endif

    /*
     * 使用用户提供的别名和/或实际列名构建有效列名列表。
     */
    rte->eref = makeAlias(refname, NIL);
    buildRelationAliases(rel->rd_att, alias, rte->eref);

    /*
     * 访问检查的初始默认值始终为CHECK-FOR-READ-access，
     * 这对于除了目标表以外的所有情况都是正确的。
     */
    set_rte_flags(rte, inh, inFromCl, ACL_SELECT);
    rte->lateral = false;

    setRteOrientation(rel, rte);

    /*
     * 将完成的RTE添加到pstate的范围表列表中，但不要添加到连接列表或命名空间中 - 调用者必须在适当的位置执行。
     */
    if (pstate != NULL) {
        pstate->p_rtable = lappend(pstate->p_rtable, rte);
        /*
         * 如果添加到p_rtable的rte由同义词对象引用，
         * 则标记pstate->p_hasSynonyms。
         */
        if (!pstate->p_hasSynonyms && OidIsValid(rte->refSynOid)) {
            pstate->p_hasSynonyms = true;
        }
    }

    return rte;
}

/*
 * 将子查询的条目添加到解析状态的范围表（p_rtable）中
 *
 * 与addRangeTableEntry()函数类似，但它创建一个子查询的RangeTblEntry。
 * 注意：必须提供别名子句。
 */
RangeTblEntry* addRangeTableEntryForSubquery(
    ParseState* pstate, Query* subquery, Alias* alias, bool lateral, bool inFromCl, bool sublinkPullUp)
{
    RangeTblEntry* rte = makeNode(RangeTblEntry);
    char* refname = NULL;
    Alias* eref = NULL;
    int numaliases;
    int varattno;
    ListCell* tlistitem = NULL;

    Alias* query_alias = alias;

    if (subquery == NULL) {
        ereport(
            ERROR, (errmodule(MOD_OPT), errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED), errmsg("subquery can not be NULL")));
    }

    // 处理子查询中的别名，以用作RangeTblEntry的引用名
    if (sublinkPullUp && subquery->hintState && subquery->hintState->block_name_hint != NULL) {
        BlockNameHint* block_name_hint = (BlockNameHint*)linitial(subquery->hintState->block_name_hint);

        block_name_hint->base.state = HINT_STATE_USED;

        char* block_name = strVal(linitial(block_name_hint->base.relnames));

        query_alias = makeAlias(block_name, NIL);
    }

    refname = query_alias->aliasname;
    rte->rtekind = RTE_SUBQUERY;
    rte->relid = InvalidOid;
    rte->subquery = subquery;
    rte->alias = query_alias;
    rte->sublink_pull_up = sublinkPullUp;
    rte->orientation = REL_ORIENT_UNKNOWN;
    eref = (Alias*)copyObject(query_alias);
    numaliases = list_length(eref->colnames);

    /* 填充未指定别名列的任何列 */
    varattno = 0;
    foreach (tlistitem, subquery->targetList) {
        TargetEntry* te = (TargetEntry*)lfirst(tlistitem);

        if (te->resjunk) {
            continue;
        }
        varattno++;
        AssertEreport(varattno == te->resno, MOD_OPT, "");
        if (varattno > numaliases) {
            char* attrname = NULL;

            if (te->resname != NULL &&
                IsQuerySWCBRewrite(subquery) &&
                strstr(te->resname, "@")) {
                rte->swSubExist = true;

                char *label = strrchr(te->resname, '@');
                label += 1;
                attrname = pstrdup(label);
            } else {
                attrname = pstrdup(te->resname);
            }

            eref->colnames = lappend(eref->colnames, makeString(attrname));
        }
    }
    if (varattno < numaliases) {
        ereport(ERROR,
            (errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
                errmsg(
                    "table \"%s\" has %d columns available but %d columns specified", refname, varattno, numaliases)));
    }

    rte->eref = eref;

    /*
     * 子查询不会检查访问权限。
     */
    set_rte_flags(rte, false, inFromCl, 0);
    rte->lateral = lateral;

    /*
     * 将完成的RTE添加到pstate的范围表列表中，但不添加到连接列表或命名空间中 --- 如果适用，调用者必须执行这一步。
     */
    if (pstate != NULL) {
        pstate->p_rtable = lappend(pstate->p_rtable, rte);
    }

    return rte;
}

/*
 * 将函数的条目添加到解析状态的范围表（p_rtable）中
 *
 * 与addRangeTableEntry()函数类似，但它创建一个函数的RangeTblEntry。
 */
RangeTblEntry* addRangeTableEntryForFunction(
    ParseState* pstate, char* funcname, Node* funcexpr, RangeFunction* rangefunc, bool lateral, bool inFromCl)
{
    RangeTblEntry* rte = makeNode(RangeTblEntry);
    TypeFuncClass functypclass;
    Oid funcrettype;
    TupleDesc tupdesc;
    Alias* alias = rangefunc->alias;
    List* coldeflist = rangefunc->coldeflist;
    Alias* eref = NULL;

    rte->rtekind = RTE_FUNCTION;
    rte->relid = InvalidOid;
    rte->subquery = NULL;
    rte->funcexpr = funcexpr;
    rte->funccoltypes = NIL;
    rte->funccoltypmods = NIL;
    rte->funccolcollations = NIL;
    rte->alias = alias;

    eref = makeAlias(alias ? alias->aliasname : funcname, NIL);
    rte->eref = eref;

    /*
     * 现在确定函数是返回简单类型还是复合类型。
     */
    functypclass = get_expr_result_type(funcexpr, &funcrettype, &tupdesc);

    /*
     * 如果函数返回RECORD并且没有预定的记录类型，则需要coldeflist，否则不允许。
     */
    if (coldeflist != NIL) {
        if (functypclass != TYPEFUNC_RECORD) {
            ereport(ERROR,
                (errcode(ERRCODE_SYNTAX_ERROR),
                    errmsg("a column definition list is only allowed for functions returning \"record\""),
                    parser_errposition(pstate, exprLocation(funcexpr))));
        }
    } else {
        if (functypclass == TYPEFUNC_RECORD) {
            ereport(ERROR,
                (errcode(ERRCODE_SYNTAX_ERROR),
                    errmsg("a column definition list is required for functions returning \"record\""),
                    parser_errposition(pstate, exprLocation(funcexpr))));
        }
    }

    if (functypclass == TYPEFUNC_COMPOSITE) {
        /* 复合数据类型，例如表的行类型 */
        AssertEreport(tupdesc, MOD_OPT, "");
        /* 构建列别名列表 */
        buildRelationAliases(tupdesc, alias, eref);
    } else if (functypclass == TYPEFUNC_SCALAR) {
        /* 基本数据类型，即标量 */
        buildScalarFunctionAlias(funcexpr, funcname, alias, eref);
    } else if (functypclass == TYPEFUNC_RECORD) {
        ListCell* col = NULL;

        /*
         * 使用列定义列表来形成别名列表和funccoltypes/funccoltypmods/funccolcollations列表。
         */
        foreach (col, coldeflist) {
            ColumnDef* n = (ColumnDef*)lfirst(col);
            char* attrname = NULL;
            Oid attrtype;
            int32 attrtypmod;
            Oid attrcollation;

            attrname = pstrdup(n->colname);
            if (n->typname->setof) {
                ereport(ERROR,
                    (errcode(ERRCODE_INVALID_TABLE_DEFINITION),
                        errmsg("column \"%s\" cannot be declared SETOF", attrname),
                        parser_errposition(pstate, n->typname->location)));
            }
            typenameTypeIdAndMod(pstate, n->typname, &attrtype, &attrtypmod);
            attrcollation = GetColumnDefCollation(pstate, n, attrtype);
            eref->colnames = lappend(eref->colnames, makeString(attrname));
            rte->funccoltypes = lappend_oid(rte->funccoltypes, attrtype);
            rte->funccoltypmods = lappend_int(rte->funccoltypmods, attrtypmod);
            rte->funccolcollations = lappend_oid(rte->funccolcollations, attrcollation);
        }
    } else {
        ereport(ERROR,
            (errcode(ERRCODE_DATATYPE_MISMATCH),
                errmsg("function \"%s\" in FROM has unsupported return type %s", funcname, format_type_be(funcrettype)),
                parser_errposition(pstate, exprLocation(funcexpr))));
    }

    /*
     * 函数永远不会检查访问权限（至少不是通过RTE权限机制检查的）。
     */
    set_rte_flags(rte, false, inFromCl, 0);
    rte->lateral = lateral;

    /*
     * 将完成的RTE添加到pstate的范围表列表中，但不添加到连接列表或命名空间中 --- 如果适用，调用者必须执行这一步。
     */
    if (pstate != NULL) {
        pstate->p_rtable = lappend(pstate->p_rtable, rte);
    }

    return rte;
}

/*
 * 向解析状态的范围表（p_rtable）中添加一个 VALUES 列表的范围表项。
 * VALUES 列表是一种表示一组值的集合的特殊查询结构。
 */
RangeTblEntry* addRangeTableEntryForValues(
    ParseState* pstate, List* exprs, List* collations, Alias* alias, bool inFromCl)
{
    RangeTblEntry* rte = makeNode(RangeTblEntry);
    char* refname = alias ? alias->aliasname : pstrdup("*VALUES*");
    Alias* eref = NULL;
    int numaliases;
    int numcolumns;

    rte->rtekind = RTE_VALUES;
    rte->relid = InvalidOid;
    rte->subquery = NULL;
    rte->values_lists = exprs;
    rte->values_collations = collations;
    rte->alias = alias;
    rte->orientation = REL_ROW_ORIENTED;

    eref = alias ? (Alias*)copyObject(alias) : makeAlias(refname, NIL);

    /* 填充任何未指定的别名列 */
    numcolumns = list_length((List*)linitial(exprs));
    numaliases = list_length(eref->colnames);
    while (numaliases < numcolumns) {
        char attrname[64] = {0};

        numaliases++;
        errno_t rc = snprintf_s(attrname, sizeof(attrname), sizeof(attrname) - 1, "column%d", numaliases);
        securec_check_ss(rc, "\0", "\0");
        eref->colnames = lappend(eref->colnames, makeString(pstrdup(attrname)));
    }
    if (numcolumns < numaliases) {
        ereport(ERROR,
            (errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
                errmsg("VALUES 列表 \"%s\" 有 %d 列可用，但指定了 %d 列",
                    refname,
                    numcolumns,
                    numaliases)));
    }

    rte->eref = eref;

    /*
     * 子查询不会检查访问权限。
     */
    set_rte_flags(rte, false, inFromCl, 0);
    rte->lateral = false;

    /*
     * 将完成的范围表项添加到解析状态的范围表列表中，
     * 但不包括到连接列表或命名空间中，需要调用者在适当的时候完成这些操作。
     */
    if (pstate != NULL) {
        pstate->p_rtable = lappend(pstate->p_rtable, rte);
    }

    return rte;
}

/*
 * 向解析状态的范围表（p_rtable）中添加一个 JOIN 操作的范围表项。
 * JOIN 操作用于将多个表关联起来。
 */
RangeTblEntry* addRangeTableEntryForJoin(
    ParseState* pstate, List* colnames, JoinType jointype, List* aliasvars, Alias* alias, bool inFromCl)
{
    RangeTblEntry* rte = makeNode(RangeTblEntry);
    Alias* eref = NULL;
    int numaliases;

    /*
     * 如果 JOIN 有太多的列，则报错 ---
     * 我们必须能够使用 AttrNumber 引用任何列。
     */
    if (list_length(aliasvars) > MaxAttrNumber) {
        ereport(ERROR,
            (errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
                errmsg("JOIN 最多可以有 %d 列", MaxAttrNumber)));
    }

    rte->rtekind = RTE_JOIN;
    rte->relid = InvalidOid;
    rte->subquery = NULL;
    rte->jointype = jointype;
    rte->joinaliasvars = aliasvars;
    rte->alias = alias;
    rte->orientation = REL_ORIENT_UNKNOWN;

    eref = alias ? (Alias*)copyObject(alias) : makeAlias("unnamed_join", NIL);
    numaliases = list_length(eref->colnames);
    /* 填充任何未指定的别名列 */
    if (numaliases < list_length(colnames)) {
        eref->colnames = list_concat(eref->colnames, list_copy_tail(colnames, numaliases));
    }

    rte->eref = eref;

    /* JOIN 操作不会检查访问权限。*/
    set_rte_flags(rte, false, inFromCl, 0);
    rte->lateral = false;

    /*
     * 将完成的范围表项添加到解析状态的范围表列表中，
     * 但不包括到连接列表或命名空间中，需要调用者在适当的时候完成这些操作。
     */
    if (pstate != NULL) {
        pstate->p_rtable = lappend(pstate->p_rtable, rte);
    }

    return rte;
}

/*
 * 向解析状态的范围表（p_rtable）中添加一个 CTE 引用的范围表项。
 * CTE 是一种命名的临时结果集，可以在查询中多次引用。
 */
RangeTblEntry* addRangeTableEntryForCTE(
    ParseState* pstate, CommonTableExpr* cte, Index levelsup, RangeVar* rv, bool inFromCl)
{
    RangeTblEntry* rte = makeNode(RangeTblEntry);
    Alias* alias = rv->alias;
    char* refname = alias ? alias->aliasname : cte->ctename;
    Alias* eref = NULL;
    int numaliases;
    int varattno;
    ListCell* lc = NULL;

    rte->rtekind = RTE_CTE;
    rte->ctename = cte->ctename;
    rte->ctelevelsup = levelsup;
    if (levelsup > 0) {
        cte->referenced_by_subquery = true;
    }

    /* 只有在 CTE 的解析分析未完成时才是自引用 */
    rte->self_reference = !IsA(cte->ctequery, Query);
    cte->self_reference = rte->self_reference;
    rte->cterecursive = cte->cterecursive;
    AssertEreport(cte->cterecursive || !rte->self_reference, MOD_OPT, "");
    /* 如果不是自引用，则增加 CTE 的引用计数 */
    if (!rte->self_reference) {
        cte->cterefcount++;
    }

    /*
     * 如果 CTE 是 INSERT/UPDATE/DELETE 而没有 RETURNING 子句，则报错。
     * 在自引用的情况下不会检查这个，但这没关系，因为不允许递归的数据修改 CTE。
     */
    if (IsA(cte->ctequery, Query)) {
        Query* ctequery = (Query*)cte->ctequery;

        if (ctequery->commandType != CMD_SELECT && ctequery->returningList == NIL) {
            ereport(ERROR,
                (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                    errmsg("WITH 查询 \"%s\" 没有 RETURNING 子句", cte->ctename),
                    parser_errposition(pstate, rv->location)));
        }
    }

    rte->ctecoltypes = cte->ctecoltypes;
    rte->ctecoltypmods = cte->ctecoltypmods;
    rte->ctecolcollations = cte->ctecolcollations;

    rte->alias = alias;
    if (alias != NULL) {
        eref = (Alias*)copyObject(alias);
    } else {
        eref = makeAlias(refname, NIL);
    }
    numaliases = list_length(eref->colnames);

    /* 填充任何未指定的别名列 */
    varattno = 0;
    foreach (lc, cte->ctecolnames) {
        varattno++;
        if (varattno > numaliases) {
            eref->colnames = lappend(eref->colnames, lfirst(lc));
        }
    }
    if (varattno < numaliases) {
        ereport(ERROR,
            (errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
                errmsg(
                    "表 \"%s\" 有 %d 列可用，但指定了 %d 列", refname, varattno, numaliases)));
    }

    rte->eref = eref;

    /* ----------
     * 标志：
     * - 这个 RTE 应该展开以包含子代表，
     * - 这个 RTE 在 FROM 子句中，
     * - 这个 RTE 应该检查适当的访问权限。
     *
     * 子查询不会检查访问权限。
     * ----------
     */
    rte->lateral = false;
    rte->inh = false; /* 子查询永远不会是 true */
    rte->inFromCl = inFromCl;

    rte->requiredPerms = 0;
    rte->checkAsUser = InvalidOid;
    rte->selectedCols = NULL;
    rte->insertedCols = NULL;
    rte->updatedCols = NULL;
    rte->extraUpdatedCols = NULL;
    rte->orientation = REL_ORIENT_UNKNOWN;

    /*
     * 将完成的范围表项添加到解析状态的范围表列表中，
     * 但不包括到连接列表或命名空间中，需要调用者在适当的时候完成这些操作。
     */
    if (pstate != NULL) {
        pstate->p_rtable = lappend(pstate->p_rtable, rte);
    }

    /*
     * 如果 CTE 从 startwith/connectby 重写而来，我们需要添加伪列，
     * 因为它从子级返回解析树，不包含伪列信息。
     */
    if (cte->swoptions != NULL && IsA(cte->ctequery, Query) && pstate != NULL) {
        AddStartWithCTEPseudoReturnColumns(cte, rte, list_length(pstate->p_rtable));
    }

    return rte;
}

/*
 * 根据关系构建范围表项
 */
RangeTblEntry* getRangeTableEntryByRelation(Relation rel)
{
    // 创建范围表项
    RangeTblEntry* rte = makeNode(RangeTblEntry);
    // 获取关系的引用名称
    char* refname = RelationGetRelationName(rel);

    // 设置范围表项的基本属性
    rte->rtekind = RTE_RELATION;
    rte->alias = NULL;
    rte->relid = RelationGetRelid(rel);
    rte->relkind = rel->rd_rel->relkind;
    rte->ispartrel = RELATION_IS_PARTITIONED(rel);
    rte->relhasbucket = RELATION_HAS_BUCKET(rel);
    rte->bucketmapsize = rel->rd_bucketmapsize;
    rte->isexcluded = false;
    rte->refSynOid = rel->rd_refSynOid;

#ifdef PGXC
    // 处理分布式场景下的相关属性
    rte->relname = pstrdup(RelationGetRelationName(rel));
    rte->partAttrNum = get_rte_part_attr_num(rel);
#endif

    /*
     * 构建有效列名列表，使用用户提供的别名和/或实际列名
     */
    rte->eref = makeAlias(refname, NIL);
    buildRelationAliases(rel->rd_att, rte->alias, rte->eref);

    /*
     * 访问权限检查的初始默认值总是检查读取权限，
     * 这对于除目标表之外的所有情况都是正确的。
     */
    rte->inh = true; /* 对于联接而言永远不是 true */
    rte->inFromCl = true;
    rte->requiredPerms = ACL_SELECT;
    rte->checkAsUser = InvalidOid;
    rte->selectedCols = NULL;
    rte->insertedCols = NULL;
    rte->updatedCols = NULL;
    rte->lateral = false;
    rte->extraUpdatedCols = NULL;

    // 设置范围表项的方向属性
    setRteOrientation(rel, rte);

    return rte;
}

/*
 * 判断指定的 refname 是否被选择为 FOR UPDATE/FOR SHARE
 *
 * 在我们尚未执行 transformLockingClause 时使用，
 * 但需要在打开关系时知道正确的锁。
 */
bool isLockedRefname(ParseState* pstate, const char* refname)
{
    ListCell* l = NULL;

    /*
     * 如果我们处于从父级锁定的子查询中，
     * 则表现为就像这里有一个通用的 FOR UPDATE 一样。
     */
    if (pstate->p_locked_from_parent) {
        return true;
    }

    // 遍历锁定子句，查看指定的 refname 是否被选择
    foreach (l, pstate->p_locking_clause) {
        LockingClause* lc = (LockingClause*)lfirst(l);

        if (lc->lockedRels == NIL) {
            /* 查询中使用的所有表 */
            return true;
        } else {
            /* 仅限定名的表 */
            ListCell* l2 = NULL;

            foreach (l2, lc->lockedRels) {
                RangeVar* thisrel = (RangeVar*)lfirst(l2);

                if (strcmp(refname, thisrel->relname) == 0) {
                    return true;
                }
            }
        }
    }
    return false;
}

/*
 * 将给定的范围表项作为顶级条目添加到解析状态的 join list 和/或 name space lists
 */
void addRTEtoQuery(
    ParseState* pstate, RangeTblEntry* rte, bool addToJoinList, bool addToRelNameSpace, bool addToVarNameSpace)
{
    // 将范围表项添加到 join list 中
    if (addToJoinList) {
        int rtindex = RTERangeTablePosn(pstate, rte, NULL);
        RangeTblRef* rtr = makeNodeFast(RangeTblRef);

        rtr->rtindex = rtindex;
        pstate->p_joinlist = lappend(pstate->p_joinlist, rtr);
    }
    
    // 将范围表项添加到 rel name space 或 var name space 中
    if (addToRelNameSpace || addToVarNameSpace) {
        ParseNamespaceItem* nsitem;

        // 创建解析命名空间条目
        nsitem = (ParseNamespaceItem*)palloc(sizeof(ParseNamespaceItem));
        nsitem->p_rte = rte;
        nsitem->p_lateral_only = false;
        nsitem->p_lateral_ok = true;
        
        // 将解析命名空间条目添加到 rel name space 中
        if (addToRelNameSpace)
            pstate->p_relnamespace = lappend(pstate->p_relnamespace, nsitem);
        
        // 将解析命名空间条目添加到 var name space 中
        if (addToVarNameSpace)
            pstate->p_varnamespace = lappend(pstate->p_varnamespace, nsitem);
    }
}


/*
 * expandRTE -- 扩展范围表项的列
 *
 * 这个函数创建一个范围表项（RTE）的列名列表（如果提供别名则使用别名，否则使用实际名称）以及每个列的 Vars 列表。
 * 仅考虑用户列。如果 include_dropped 是 FALSE，则结果中将省略已删除的列。
 * 如果 include_dropped 是 TRUE，则已删除的列将返回空字符串和 NULL 常量（而不是 Vars）。
 *
 * rtindex、sublevels_up 和 location 是在创建的 Vars 中使用的 varno、varlevelsup 和 location 值。
 * 通常，rtindex 应该与其 rangetable 中的实际位置相匹配。
 *
 * 输出列表存储在 *colnames 和 *colvars 中。如果只需要两种输出列表中的一种，请为不需要的输出指针传递 NULL。
 */
void expandRTE(RangeTblEntry* rte, int rtindex, int sublevels_up, int location, bool include_dropped, List** colnames,
    List** colvars, ParseState* pstate)
{
    int varattno;

    if (colnames != NULL) {
        *colnames = NIL;
    }
    if (colvars != NULL) {
        *colvars = NIL;
    }

    switch (rte->rtekind) {
        case RTE_RELATION:
            /* 普通关系 RTE */
            expandRelation(rte->relid, rte->eref, rtindex, sublevels_up, location, include_dropped, colnames, colvars);
            break;
        case RTE_SUBQUERY: {
            /* 子查询 RTE */
            ListCell* aliasp_item = list_head(rte->eref->colnames);
            ListCell* tlistitem = NULL;

            varattno = 0;
            foreach (tlistitem, rte->subquery->targetList) {
                TargetEntry* te = (TargetEntry*)lfirst(tlistitem);

                if (te->resjunk) {
                    continue;
                }
                varattno++;
                AssertEreport(varattno == te->resno, MOD_OPT, "");

                /*
                 * 在外部查询最初解析时，子查询的 tlist 中可能包含了外部查询不需要的额外列。
                 * 我们应该忽略这些额外的列，类似于复合返回函数的行为，在 RTE_FUNCTION 的情况下会进行比较。
                 */
                if (aliasp_item == NULL) {
                    break;
                }

                if (colnames != NULL) {
                    char* label = strVal(lfirst(aliasp_item));

                    *colnames = lappend(*colnames, makeString(pstrdup(label)));
                }

                if (colvars != NULL) {
                    Var* varnode = NULL;

                    varnode = makeVar(rtindex,
                        varattno,
                        exprType((Node*)te->expr),
                        exprTypmod((Node*)te->expr),
                        exprCollation((Node*)te->expr),
                        sublevels_up);
                    varnode->location = location;

                    *colvars = lappend(*colvars, varnode);
                }

                aliasp_item = lnext(aliasp_item);
            }
        } break;
        case RTE_FUNCTION: {
            /* 函数 RTE */
            TypeFuncClass functypclass;
            Oid funcrettype = InvalidOid;
            TupleDesc tupdesc;
            int4 funcrettype_orig = -1;

            functypclass = get_expr_result_type(rte->funcexpr, &funcrettype, &tupdesc, &funcrettype_orig);
            if (functypclass == TYPEFUNC_COMPOSITE) {
                /* 复合数据类型，例如表的行类型 */
                AssertEreport(tupdesc, MOD_OPT, "");
                expandTupleDesc(
                    tupdesc, rte->eref, rtindex, sublevels_up, location, include_dropped, colnames, colvars);
            } else if (functypclass == TYPEFUNC_SCALAR) {
                /* 基本数据类型，即标量 */
                if (colnames != NULL) {
                    *colnames = lappend(*colnames, linitial(rte->eref->colnames));
                }

                if (colvars != NULL) {
                    Var* varnode = NULL;

                    varnode =
                        makeVar(rtindex, 1, funcrettype, funcrettype_orig, exprCollation(rte->funcexpr), sublevels_up);
                    varnode->location = location;

                    *colvars = lappend(*colvars, varnode);
                }
            } else if (functypclass == TYPEFUNC_RECORD) {
                if (colnames != NULL) {
                    *colnames = (List*)copyObject(rte->eref->colnames);
                }
                if (colvars != NULL) {
                    ListCell* l1 = NULL;
                    ListCell* l2 = NULL;
                    ListCell* l3 = NULL;
                    int attnum = 0;

                    forthree(l1, rte->funccoltypes, l2, rte->funccoltypmods, l3, rte->funccolcollations)
                    {
                        Oid attrtype = lfirst_oid(l1);
                        int32 attrtypmod = lfirst_int(l2);
                        Oid attrcollation = lfirst_oid(l3);
                        Var* varnode = NULL;

                        attnum++;
                        varnode = makeVar(rtindex, attnum, attrtype, attrtypmod, attrcollation, sublevels_up);
                        varnode->location = location;
                        *colvars = lappend(*colvars, varnode);
                    }
                }
            } else {
                /* addRangeTableEntryForFunction 应该捕获到这种情况 */
                ereport(ERROR,
                    (errcode(ERRCODE_FEATURE_NOT_SUPPORTED), errmsg("function in FROM has unsupported return type")));
            }
        } break;
        case RTE_VALUES: {
            /* Values RTE */
            ListCell* aliasp_item = list_head(rte->eref->colnames);
            int32* coltypmods = NULL;
            ListCell* lcv = NULL;
            ListCell* lcc = NULL;

            /*
             * 可以从第一行的表达式中提取列类型，因为所有行都将强制转换为相同的类型。
             * 但它们的类型修饰符可能不同，因此我们可能需要检查所有行来计算这些修饰符。
             * 列的排序在 values_collations 中预先计算。
             */
            if (colvars != NULL) {
                coltypmods = getValuesTypmods(rte);
            } else {
                coltypmods = NULL;
            }

            varattno = 0;
            forboth(lcv, (List*)linitial(rte->values_lists), lcc, rte->values_collations)
            {
                Node* col = (Node*)lfirst(lcv);
                Oid colcollation = lfirst_oid(lcc);

                varattno++;
                if (colnames != NULL) {
                    /* 假定每列有一个别名 */
                    char* label = strVal(lfirst(aliasp_item));

                    *colnames = lappend(*colnames, makeString(pstrdup(label)));
                    aliasp_item = lnext(aliasp_item);
                }

                if (colvars != NULL) {
                    Var* varnode = NULL;

                    varnode =
                        makeVar(rtindex, varattno, exprType(col), coltypmods[varattno - 1], colcollation, sublevels_up);
                    varnode->location = location;
                    *colvars = lappend(*colvars, varnode);
                }
            }
            if (coltypmods != NULL) {
                pfree_ext(coltypmods);
            }
        } break;
        case RTE_JOIN: {
            /* Join RTE */
            ListCell* colname = NULL;
            ListCell* aliasvar = NULL;

            AssertEreport(list_length(rte->eref->colnames) == list_length(rte->joinaliasvars), MOD_OPT, "");

            varattno = 0;
            forboth(colname, rte->eref->colnames, aliasvar, rte->joinaliasvars)
            {
                Node* avar = (Node*)lfirst(aliasvar);

                varattno++;

                /*
                 * 在普通解析过程中，连接中不会有任何被删除的列；
                 * 但是我们必须检查，因为这个例程也被重写器使用，而在存储规则中找到的连接可能包含对已删除列的连接。
                 * 这将由别名-vars 列表中的 NULL Const 信号传递。
                 */
                if (IsA(avar, Const)) {
                    if (include_dropped) {
                        if (colnames != NULL) {
                            *colnames = lappend(*colnames, makeString(pstrdup("")));
                        }
                        if (colvars != NULL) {
                            *colvars = lappend(*colvars, copyObject(avar));
                        }
                    }
                    continue;
                }

                if (colnames != NULL) {
                    char* label = strVal(lfirst(colname));

                    *colnames = lappend(*colnames, makeString(pstrdup(label)));
                }

                if (colvars != NULL) {
                    Var* varnode = NULL;

                    varnode =
                        makeVar(rtindex, varattno, exprType(avar), exprTypmod(avar), exprCollation(avar), sublevels_up);
                    varnode->location = location;

                    *colvars = lappend(*colvars, varnode);
                }
            }
        } break;
        case RTE_CTE: {
            ListCell* aliasp_item = list_head(rte->eref->colnames);
            ListCell* lct = NULL;
            ListCell* lcm = NULL;
            ListCell* lcc = NULL;

            varattno = 0;
            forthree(lct, rte->ctecoltypes, lcm, rte->ctecoltypmods, lcc, rte->ctecolcollations)
            {
                Oid coltype = lfirst_oid(lct);
                int32 coltypmod = lfirst_int(lcm);
                Oid colcoll = lfirst_oid(lcc);

                if (colnames != NULL) {
                    /* 假设每个输出列有一个别名 */
                    char* label = strVal(lfirst(aliasp_item));

                    if (rte->swConverted) {
                        /* 在 RTE 扩展的 CTE 案例中，跳过伪返回列 */
                        if (IsPseudoReturnColumn(label)) {
                            continue;
                        }

                        label = ReplaceSWCTEOutSrting(pstate, rte, label);
                    }

                    *colnames = lappend(*colnames, makeString(pstrdup(label)));
                    aliasp_item = lnext(aliasp_item);
                }

                /* 计数 varattno */
                varattno++;

                if (colvars != NULL) {
                    Var* varnode = NULL;

                    varnode = makeVar(rtindex, varattno, coltype, coltypmod, colcoll, sublevels_up);
                    varnode->location = location;

                    *colvars = lappend(*colvars, varnode);
                }
            }
        } break;
        case RTE_RESULT:
            /* 这些不暴露任何列，因此什么都不需要做 */
            break;
        default:
            ereport(ERROR,
                (errcode(ERRCODE_UNRECOGNIZED_NODE_TYPE), errmsg("unrecognized RTE kind: %d", (int)rte->rtekind)));
    }
}


/*
 * expandRelation -- expandRTE subroutine
 */
static void expandRelation(Oid relid, Alias* eref, int rtindex, int sublevels_up, int location, bool include_dropped,
    List** colnames, List** colvars)
{
    Relation rel;

    /* Get the tupledesc and turn it over to expandTupleDesc */
    rel = relation_open(relid, AccessShareLock);
    expandTupleDesc(rel->rd_att, eref, rtindex, sublevels_up, location, include_dropped, colnames, colvars);
    relation_close(rel, AccessShareLock);
}

/*
 * expandTupleDesc -- expandRTE 子例程
 */
static void expandTupleDesc(TupleDesc tupdesc, Alias* eref, int rtindex, int sublevels_up, int location,
    bool include_dropped, List** colnames, List** colvars)
{
    int maxattrs = tupdesc->natts;
    int numaliases = list_length(eref->colnames);
    int varattno;

    for (varattno = 0; varattno < maxattrs; varattno++) {
        Form_pg_attribute attr = &tupdesc->attrs[varattno];

        if (attr->attisdropped) {
            if (include_dropped) {
                if (colnames != NULL) {
                    *colnames = lappend(*colnames, makeString(pstrdup("")));
                }
                if (colvars != NULL) {
                    /*
                     * 在这里不能使用 atttypid，但 Const 它声称是什么类型并不重要。
                     */
                    *colvars = lappend(*colvars, makeNullConst(INT4OID, -1, InvalidOid));
                }
            }
            continue;
        }

        /* 跳过时序相关关系的隐藏列 */
        if (TsRelWithImplDistColumn(tupdesc->attrs, varattno)) {
            continue;
        }

        if (colnames != NULL) {
            char* label = NULL;

            if (varattno < numaliases) {
                label = strVal(list_nth(eref->colnames, varattno));
            } else {
                label = NameStr(attr->attname);
            }
            *colnames = lappend(*colnames, makeString(pstrdup(label)));
        }

        if (colvars != NULL) {
            Var* varnode = NULL;

            varnode = makeVar(rtindex, attr->attnum, attr->atttypid, attr->atttypmod, attr->attcollation, sublevels_up);
            varnode->location = location;

            *colvars = lappend(*colvars, varnode);
        }
    }
}

/*
 * getValuesTypmods -- expandRTE 子例程
 *
 * 为给定的 VALUES RTE 扩展每列的类型修饰符。返回一个 palloc'd 数组。
 */
static int32* getValuesTypmods(RangeTblEntry* rte)
{
    int32* coltypmods = NULL;
    List* firstrow = NIL;
    int ncolumns, nvalid, i;
    ListCell* lc = NULL;

    AssertEreport(rte->values_lists != NIL, MOD_OPT, "");
    firstrow = (List*)linitial(rte->values_lists);
    ncolumns = list_length(firstrow);
    coltypmods = (int32*)palloc(ncolumns * sizeof(int32));
    nvalid = 0;

    /* 从第一行 VALUES 中收集类型修饰符 */
    i = 0;
    foreach (lc, firstrow) {
        Node* col = (Node*)lfirst(lc);

        coltypmods[i] = exprTypmod(col);
        if (coltypmods[i] >= 0) {
            nvalid++;
        }
        i++;
    }

    /*
     * 扫描剩余行；一旦对于某一列我们有了一个不匹配的类型修饰符，
     * 就将该类型修饰符重置为 -1。如果所有类型修饰符都变为 -1，我们就可以提前退出。
     */
    if (nvalid > 0) {
        for_each_cell(lc, lnext(list_head(rte->values_lists)))
        {
            List* thisrow = (List*)lfirst(lc);
            ListCell* lc2 = NULL;

            AssertEreport(list_length(thisrow) == ncolumns, MOD_OPT, "");
            i = 0;
            foreach (lc2, thisrow) {
                Node* col = (Node*)lfirst(lc2);

                if (coltypmods[i] >= 0 && coltypmods[i] != exprTypmod(col)) {
                    coltypmods[i] = -1;
                    nvalid--;
                }
                i++;
            }

            if (nvalid <= 0) {
                break;
            }
        }
    }

    return coltypmods;
}

/*
 * expandRelAttrs -
 *	  "*" 扩展的工作函数：为 RTE 的属性生成目标条目的列表
 *
 * 与 expandRTE 一样，rtindex/sublevels_up 确定所产生的 Vars 的 varno/varlevelsup 字段，
 * location 设置它们的位置。pstate->p_next_resno 确定分配给 TLEs 的 resnos。对于引用的列，
 * 标记为需要 SELECT 权限。
 */
List* expandRelAttrs(ParseState* pstate, RangeTblEntry* rte, int rtindex, int sublevels_up, int location)
{
    List *names = NIL;
    List *vars = NIL;
    ListCell *name = NULL;
    ListCell *var = NULL;
    List* te_list = NIL;
    bool is_ledger = is_ledger_usertable(rte->relid);

    expandRTE(rte, rtindex, sublevels_up, location, false, &names, &vars, pstate);

    /*
     * 要求对表进行读访问。通常这与下面的 markVarForSelectPriv 调用冗余，
     * 但如果表有零列则不是这样。
     */
    rte->requiredPerms |= ACL_SELECT;

    forboth(name, names, var, vars)
    {
        char* label = strVal(lfirst(name));
        if (is_ledger && strcmp(label, "hash") == 0) {
            continue;
        }
        Var* varnode = (Var*)lfirst(var);
        TargetEntry* te = NULL;

        te = makeTargetEntry((Expr*)varnode, (AttrNumber)pstate->p_next_resno++, label, false);
        te_list = lappend(te_list, te);

        /* 要求对每列进行读访问 */
        markVarForSelectPriv(pstate, varnode, rte);
    }

    AssertEreport(name == NULL && var == NULL, MOD_OPT, ""); /* 列表长度不一致？ */

    return te_list;
}


/*
 * get_rte_attribute_name
 *		从 RangeTblEntry 中获取属性名
 *
 * 与 get_attname() 不同，因为我们使用可用的别名。
 * 特别是，它适用于子查询或连接的 RTE，而 get_attname() 仅适用于真实关系。
 *
 * 如果给定的 attnum 是 InvalidAttrNumber，则返回 "*"
 * --- 在这种情况下，当 Var 代表关系的整个元组时会发生。
 *
 * 使用后必须释放指针！！！
 */
char* get_rte_attribute_name(RangeTblEntry* rte, AttrNumber attnum, bool allowDropped)
{
    if (attnum == InvalidAttrNumber) {
        return pstrdup("*");
    }

    /*
     * 如果存在用户写的列别名，则使用它。
     */
    if (rte->alias && attnum > 0 && attnum <= list_length(rte->alias->colnames)) {
        return pstrdup(strVal(list_nth(rte->alias->colnames, attnum - 1)));
    }

    /*
     * 如果 RTE 是关系（表），则访问系统目录而不是 eref->colnames 列表。
     * 这可能会慢一点，但如果列自从 eref 列表构建以来已重命名，它将给出正确的答案（对于规则来说这很容易发生）。
     */
    if (rte->rtekind == RTE_RELATION) {
        return get_relid_attribute_name(rte->relid, attnum, allowDropped);
    }

    /*
     * 否则使用 eref 中的列名。应该总是有一个。
     */
    if (attnum > 0 && attnum <= list_length(rte->eref->colnames)) {
        return pstrdup(strVal(list_nth(rte->eref->colnames, attnum - 1)));
    }

    /* 否则，调用者给了我们一个错误的 attnum */
    ereport(ERROR,
        (errcode(ERRCODE_FDW_INVALID_ATTRIBUTE_VALUE),
            errmsg("invalid attnum %d for rangetable entry %s", attnum, rte->eref->aliasname)));
    return NULL; /* 保持编译器安静 */
}

/*
 * get_rte_attribute_type
 *		从RangeTblEntry获取属性的类型/typmod/collation信息
 */
void get_rte_attribute_type(RangeTblEntry* rte, AttrNumber attnum, Oid* vartype,
                            int32* vartypmod, Oid* varcollid, int* kvtype)
{
    switch (rte->rtekind) {
        case RTE_RELATION: {
            /* 普通关系RTE --- 获取属性的类型信息 */
            HeapTuple tp;
            Form_pg_attribute att_tup;

            tp = SearchSysCache2(ATTNUM, ObjectIdGetDatum(rte->relid), Int16GetDatum(attnum));
            if (!HeapTupleIsValid(tp)) {
                /* 不应该发生 */
                ereport(ERROR,
                    (errcode(ERRCODE_CACHE_LOOKUP_FAILED),
                        errmsg("cache lookup failed for attribute %d of relation %u", attnum, rte->relid)));
            }
            att_tup = (Form_pg_attribute)GETSTRUCT(tp);
            /*
             * 如果是删除的列，则假装它不存在。参见scanRTEForColumn中的说明。
             */
            if (att_tup->attisdropped) {
                ereport(ERROR,
                    (errcode(ERRCODE_UNDEFINED_COLUMN),
                        errmsg("column \"%s\" of relation \"%s\" does not exist",
                            NameStr(att_tup->attname),
                            get_rel_name(rte->relid))));
            }
            *vartype = att_tup->atttypid;
            *vartypmod = att_tup->atttypmod;
            *varcollid = att_tup->attcollation;
            if (kvtype != NULL && att_tup->attkvtype == ATT_KV_HIDE) {
                *kvtype = ATT_KV_HIDE;
            }
            ReleaseSysCache(tp);
        } break;
        case RTE_SUBQUERY: {
            /* 子查询RTE --- 从子查询的目标列表获取类型信息 */
            TargetEntry* te = get_tle_by_resno(rte->subquery->targetList, attnum);

            if (te == NULL || te->resjunk) {
                ereport(ERROR,
                    (errcode(ERRCODE_INVALID_ATTRIBUTE),
                        errmsg("subquery %s does not have attribute %d", rte->eref->aliasname, attnum)));
            }
            *vartype = exprType((Node*)te->expr);
            *vartypmod = exprTypmod((Node*)te->expr);
            *varcollid = exprCollation((Node*)te->expr);
        } break;
        case RTE_FUNCTION: {
            /* 函数RTE */
            TypeFuncClass functypclass;
            Oid funcrettype;
            TupleDesc tupdesc;

            functypclass = get_expr_result_type(rte->funcexpr, &funcrettype, &tupdesc);
            if (functypclass == TYPEFUNC_COMPOSITE) {
                /* 复合数据类型，例如表的行类型 */
                Form_pg_attribute att_tup;

                AssertEreport(tupdesc, MOD_OPT, "");
                /* 这可能是一个不可能发生的情况 */
                if (attnum < 1 || attnum > tupdesc->natts) {
                    ereport(ERROR,
                        (errcode(ERRCODE_UNDEFINED_COLUMN),
                            errmsg("column %d of relation \"%s\" does not exist", attnum, rte->eref->aliasname)));
                }

                att_tup = &tupdesc->attrs[attnum - 1];

                /*
                 * 如果是删除的列，则假装它不存在。参见scanRTEForColumn中的说明。
                 */
                if (att_tup->attisdropped) {
                    ereport(ERROR,
                        (errcode(ERRCODE_UNDEFINED_COLUMN),
                            errmsg("column \"%s\" of relation \"%s\" does not exist",
                                NameStr(att_tup->attname),
                                rte->eref->aliasname)));
                }
                *vartype = att_tup->atttypid;
                *vartypmod = att_tup->atttypmod;
                *varcollid = att_tup->attcollation;
                if (kvtype != NULL && att_tup->attkvtype == ATT_KV_HIDE) {
                    *kvtype = ATT_KV_HIDE;
                }
            } else if (functypclass == TYPEFUNC_SCALAR) {
                /* 基础数据类型，即标量 */
                *vartype = funcrettype;
                *vartypmod = -1;
                *varcollid = exprCollation(rte->funcexpr);
            } else if (functypclass == TYPEFUNC_RECORD) {
                *vartype = list_nth_oid(rte->funccoltypes, attnum - 1);
                *vartypmod = list_nth_int(rte->funccoltypmods, attnum - 1);
                *varcollid = list_nth_oid(rte->funccolcollations, attnum - 1);
            } else {
                /* addRangeTableEntryForFunction应该已经捕获了这个 */
                ereport(ERROR,
                    (errcode(ERRCODE_UNRECOGNIZED_NODE_TYPE), errmsg("function in FROM has unsupported return type")));
            }
        } break;
        case RTE_VALUES: {
            /*
             * Values RTE --- 我们可以从第一个子列表中获取类型信息，但是typmod可能需要扫描所有子列表，并且排序是
             * 单独存储的。使用getValuesTypmods()有点过度，但是这个路径对于VALUES来说很少走，不值得写额外的代码。
             */
            List* collist = (List*)linitial(rte->values_lists);
            Node* col = NULL;
            int32* coltypmods = getValuesTypmods(rte);

            if (attnum < 1 || attnum > list_length(collist)) {
                ereport(ERROR,
                    (errcode(ERRCODE_UNEXPECTED_NODE_STATE),
                        errmsg("values list %s does not have attribute %d", rte->eref->aliasname, attnum)));
            }
            col = (Node*)list_nth(collist, attnum - 1);
            *vartype = exprType(col);
            *vartypmod = coltypmods[attnum - 1];
            *varcollid = list_nth_oid(rte->values_collations, attnum - 1);
            pfree_ext(coltypmods);
        } break;
        case RTE_JOIN: {
            /*
             * Join RTE --- 从join RTE的别名变量获取类型信息
             */
            Node* aliasvar = NULL;

            AssertEreport(attnum > 0 && attnum <= list_length(rte->joinaliasvars), MOD_OPT, "");
            aliasvar = (Node*)list_nth(rte->joinaliasvars, attnum - 1);
            *vartype = exprType(aliasvar);
            *vartypmod = exprTypmod(aliasvar);
            *varcollid = exprCollation(aliasvar);
        } break;
        case RTE_CTE: {
            /* CTE RTE --- 从RTE的列表中获取类型信息 */
            AssertEreport(attnum > 0 && attnum <= list_length(rte->ctecoltypes), MOD_OPT, "");
            *vartype = list_nth_oid(rte->ctecoltypes, attnum - 1);
            *vartypmod = list_nth_int(rte->ctecoltypmods, attnum - 1);
            *varcollid = list_nth_oid(rte->ctecolcollations, attnum - 1);
        } break;
        case RTE_RESULT:
            /* 这可能不会发生... */
            ereport(ERROR,
                (errcode(ERRCODE_UNDEFINED_COLUMN),
                    errmsg("column %d of relation \"%s\" does not exist",
                        attnum,
                        rte->eref->aliasname)));
            break;
        default:
            ereport(ERROR,
                (errcode(ERRCODE_UNRECOGNIZED_NODE_TYPE), errmsg("unrecognized RTE kind: %d", (int)rte->rtekind)));
    }
}

/*
 * get_rte_attribute_is_dropped
 *		检查尝试引用的属性是否是已删除的列
 */
bool get_rte_attribute_is_dropped(RangeTblEntry* rte, AttrNumber attnum)
{
    bool result = false;

    switch (rte->rtekind) {
        case RTE_RELATION: {
            /* 普通关系RTE --- 获取属性的目录条目 */
            HeapTuple tp;
            Form_pg_attribute att_tup;

            tp = SearchSysCache2(ATTNUM, ObjectIdGetDatum(rte->relid), Int16GetDatum(attnum));
            if (!HeapTupleIsValid(tp)) {
                /* 不应该发生 */
                ereport(ERROR,
                    (errcode(ERRCODE_CACHE_LOOKUP_FAILED),
                        errmsg("cache lookup failed for attribute %d of relation %u", attnum, rte->relid)));
            }
            att_tup = (Form_pg_attribute)GETSTRUCT(tp);
            result = att_tup->attisdropped;
            ReleaseSysCache(tp);
        } break;
        case RTE_SUBQUERY:
        case RTE_VALUES:
        case RTE_CTE:
            /* 子查询，Values，CTE RTE永远不会有删除的列 */
            result = false;
            break;
        case RTE_JOIN: {
            /*
             * 当构建时，连接RTE不会有删除的列，但是在存储规则中的一个可能包含从底层表中删除的列，
             * 如果这些列在规则中没有明确引用的话。这将由joinaliasvars列表中的NULL Const向我们发信号。
             */
            Var* aliasvar = NULL;

            if (attnum <= 0 || attnum > list_length(rte->joinaliasvars)) {
                ereport(ERROR, (errcode(ERRCODE_UNEXPECTED_NODE_STATE), errmsg("invalid varattno %d", attnum)));
            }
            aliasvar = (Var*)list_nth(rte->joinaliasvars, attnum - 1);

            result = IsA(aliasvar, Const);
        } break;
        case RTE_FUNCTION: {
            /* 函数RTE */
            Oid funcrettype = exprType(rte->funcexpr);
            Oid funcrelid = typeidTypeRelid(funcrettype);
            if (OidIsValid(funcrelid)) {
                /*
                 * 复合数据类型，即表的行类型
                 *
                 * 与普通关系RTE相同
                 */
                HeapTuple tp;
                Form_pg_attribute att_tup;

                tp = SearchSysCache2(ATTNUM, ObjectIdGetDatum(funcrelid), Int16GetDatum(attnum));
                if (!HeapTupleIsValid(tp)) {
                    /* 不应该发生 */
                    Assert(0);
                    ereport(ERROR,
                        (errcode(ERRCODE_CACHE_LOOKUP_FAILED),
                            errmsg("cache lookup failed for attribute %d of relation %u", attnum, funcrelid)));
                }
                att_tup = (Form_pg_attribute)GETSTRUCT(tp);
                result = att_tup->attisdropped;
                ReleaseSysCache(tp);
            } else {
                /*
                 * 必须是基础数据类型，即标量
                 */
                result = false;
            }
        } break;
        case RTE_RESULT:
            /* 这可能不会发生... */
            ereport(ERROR,
                (errcode(ERRCODE_UNDEFINED_COLUMN),
                    errmsg("column %d of relation \"%s\" does not exist",
                        attnum,
                        rte->eref->aliasname)));
            result = false; /* 保持编译器安静 */
            break;
        default:
            ereport(ERROR,
                (errcode(ERRCODE_UNRECOGNIZED_NODE_TYPE), errmsg("unrecognized RTE kind: %d", (int)rte->rtekind)));
            result = false; /* 保持编译器安静 */
    }

    return result;
}


/*
 * 根据目标列表和 resno，返回匹配的 TargetEntry
 *
 * 如果 resno 在列表中不存在，返回 NULL。
 *
 * 注意：我们需要搜索而不是只是使用 list_nth() 进行索引，
 * 因为并不是所有 tlists 都按 resno 排序。
 */
TargetEntry* get_tle_by_resno(List* tlist, AttrNumber resno)
{
    ListCell* l = NULL;

    foreach (l, tlist) {
        TargetEntry* tle = (TargetEntry*)lfirst(l);

        if (tle->resno == resno) {
            return tle;
        }
    }
    return NULL;
}

/*
 * 给定一个查询和 rangetable 索引，返回关系的 RowMarkClause（如果有的话）
 *
 * 如果关系没有被选中 FOR UPDATE/SHARE，返回 NULL。
 */
RowMarkClause* get_parse_rowmark(Query* qry, Index rtindex)
{
    ListCell* l = NULL;

    foreach (l, qry->rowMarks) {
        RowMarkClause* rc = (RowMarkClause*)lfirst(l);

        if (rc->rti == rtindex) {
            return rc;
        }
    }
    return NULL;
}

/*
 * 给定关系和属性名，返回变量的属性编号
 *
 * 如果属性不存在（或已被删除），返回 InvalidAttrNumber。
 *
 * 只有在关系已经通过 heap_open() 打开的情况下才应使用这个函数。
 * 对于对非打开关系的访问，请使用缓存版本 get_attnum()。
 */
int attnameAttNum(Relation rd, const char* attname, bool sysColOK)
{
    int i;

    for (i = 0; i < rd->rd_rel->relnatts; i++) {
        Form_pg_attribute att = &rd->rd_att->attrs[i];

        if (namestrcmp(&(att->attname), attname) == 0 && !att->attisdropped) {
            return i + 1;
        }
    }

    if (sysColOK) {
        if ((i = specialAttNum(attname)) != InvalidAttrNumber) {
            if ((i != ObjectIdAttributeNumber || rd->rd_rel->relhasoids) &&
                (i != BucketIdAttributeNumber || RELATION_HAS_BUCKET(rd)) &&
                (i != UidAttributeNumber || RELATION_HAS_UIDS(rd))) {
                return i;
            }
        }
    }

    /* 失败时返回 */
    return InvalidAttrNumber;
}

/* specialAttNum()
 *
 * 检查属性名是否是 "special"，例如 "oid"。
 * - thomas 2000-02-07
 *
 * 注意：这只能发现名称是否可能是系统属性。
 * 调用者需要验证它确实是关系的属性，至少在 "oid" 的情况下，它是可选的。
 */
#ifdef PGXC
int specialAttNum(const char* attname)
#else
static int specialAttNum(const char* attname)
#endif
{
    Form_pg_attribute sysatt;

    sysatt = SystemAttributeByName(attname, true /* "oid" 将被接受 */);
    if (sysatt != NULL) {
        return sysatt->attnum;
    }
    return InvalidAttrNumber;
}

/*
 * 给定属性编号，返回该属性的名称
 *
 * 只有在关系已经通过 heap_open() 打开的情况下才应使用这个函数。
 * 对于对非打开关系的访问，请使用缓存版本 get_atttype()。
 */
Name attnumAttName(Relation rd, int attid)
{
    if (attid <= 0) {
        Form_pg_attribute sysatt;

        sysatt = SystemAttributeDefinition(attid, rd->rd_rel->relhasoids,
            RELATION_HAS_BUCKET(rd), RELATION_HAS_UIDS(rd));
        return &sysatt->attname;
    }
    if (attid > rd->rd_att->natts) {
        ereport(ERROR, (errcode(ERRCODE_INVALID_ATTRIBUTE), errmsg("无效的属性编号 %d", attid)));
    }
    return &rd->rd_att->attrs[attid - 1].attname;
}

/*
 * 给定属性编号，返回该属性的类型
 *
 * 只有在关系已经通过 heap_open() 打开的情况下才应使用这个函数。
 * 对于对非打开关系的访问，请使用缓存版本 get_atttype()。
 */
Oid attnumTypeId(Relation rd, int attid)
{
    if (attid <= 0) {
        Form_pg_attribute sysatt;

        sysatt = SystemAttributeDefinition(attid, rd->rd_rel->relhasoids,
            RELATION_HAS_BUCKET(rd), RELATION_HAS_UIDS(rd));
        return sysatt->atttypid;
    }
    if (attid > rd->rd_att->natts) {
        ereport(ERROR, (errcode(ERRCODE_INVALID_ATTRIBUTE), errmsg("无效的属性编号 %d", attid)));
    }
    return rd->rd_att->attrs[attid - 1].atttypid;
}


/*
 * 给定属性编号，返回该属性的排序规则 OID
 *
 * 只有在关系已经 heap_open() 过的情况下才能使用该函数。
 */
Oid attnumCollationId(Relation rd, int attid)
{
    if (attid <= 0) {
        /* 所有系统属性都属于不可排序的类型。*/
        return InvalidOid;
    }
    if (attid > rd->rd_att->natts) {
        ereport(ERROR, (errcode(ERRCODE_INVALID_ATTRIBUTE), errmsg("无效的属性编号 %d", attid)));
    }
    return rd->rd_att->attrs[attid - 1].attcollation;
}

/*
 * 生成有关缺失 RTE 的适当错误。
 *
 * 由于这是一种非常常见的错误类型，我们会比较努力地生成一个有帮助的消息。
 */
void errorMissingRTE(ParseState* pstate, RangeVar* relation, bool hasplus)
{
    RangeTblEntry* rte = NULL;
    int sublevels_up;
    const char* badAlias = NULL;

    /*
     * 检查查询的 rangetable 中是否有任何潜在匹配项。
     * （注意：在 RangeVar 中出现错误模式的情况会立即在这里引发错误。 这似乎没问题。）
     */
    rte = searchRangeTableForRel(pstate, relation);

    /*
     * 如果我们找到了匹配项，并且该匹配项具有别名并且别名在命名空间中可见，
     * 那么问题可能是在查询中使用了关系的实际名称而不是其别名，例如 "SELECT foo.* FROM foo f"。
     * 这个错误很常见，值得一个特定的提示。
     *
     * 如果我们找到了匹配项但不符合这些条件，假设问题是在其范围之外非法使用关系，
     * 就像 B 数据库中的 "SELECT ... FROM a, b LEFT JOIN c ON (a.x = c.y)"。
     */
    if (rte != NULL && rte->alias != NULL && strcmp(rte->eref->aliasname, relation->relname) != 0 &&
        refnameRangeTblEntry(pstate, NULL, rte->eref->aliasname, relation->location, &sublevels_up) == rte) {
        badAlias = rte->eref->aliasname;
    }

    if (rte != NULL && !hasplus) {
        ereport(ERROR,
            (errcode(ERRCODE_UNDEFINED_TABLE),
                errmsg("对表 \"%s\" 的 FROM 子句项的引用无效", relation->relname),
                (badAlias ? errhint("也许你想引用表别名 \"%s\"。", badAlias) : errhint("查询中存在表 \"%s\" 的条目，但是不能从查询的这部分引用它。", 
                rte->eref->aliasname)),
                parser_errposition(pstate, relation->location)));
    } else if (rte != NULL && hasplus) {
        ereport(ERROR,
            (errcode(ERRCODE_UNDEFINED_TABLE),
                errmsg("不能在不能从查询的这部分引用的 \"%s\" 上指定运算符 \"(+)\"。", relation->relname),
                errhint("\"%s\" 应该在当前查询级别。", rte->eref->aliasname),
                parser_errposition(pstate, relation->location)));
    } else {
        ereport(ERROR,
            (errcode(ERRCODE_UNDEFINED_TABLE),
                errmsg("缺少表 \"%s\" 的 FROM 子句项", relation->relname),
                parser_errposition(pstate, relation->location)));
    }
}

/*
 * 生成有关缺失列的适当错误。
 *
 * 由于这是一种非常常见的错误类型，我们会比较努力地生成一个有帮助的消息。
 */
void errorMissingColumn(ParseState* pstate, char* relname, char* colname, int location)
{
    RangeTblEntry* rte = NULL;

    /*
     * 如果给定了 relname，只需报告它即可。
     * （实际上，错误的合格名应该在这里结束，所以不需要在这里处理。）
     */
    if (relname) {
        char message[MAXSTRLEN];
        int rc = snprintf_s(message, MAXSTRLEN, MAXSTRLEN - 1, "列 %s.%s 不存在", relname, colname);
        securec_check_ss(rc, "", "");
        InsertErrorMessage(message, u_sess->plsql_cxt.plpgsql_yylloc, true);
        ereport(ERROR,
            (errcode(ERRCODE_UNDEFINED_COLUMN),
                errmsg("列 %s.%s 不存在", relname, colname),
                parser_errposition(pstate, location)));
    }
    /*
     * 否则，在整个 rtable 中搜索可能的匹配项。
     * 如果我们找到一个，就发出关于它的提示。
     */
    rte = searchRangeTableForCol(pstate, colname, location);

    ereport(ERROR,
        (errcode(ERRCODE_UNDEFINED_COLUMN),
            errmsg("列 \"%s\" 不存在", colname),
            rte ? errhint("表 \"%s\" 中存在名为 \"%s\" 的列，但不能从查询的这部分引用它。", rte->eref->aliasname, colname) : 0,
            parser_errposition(pstate, location)));
}

/*
 * Brief: 设置关系的存储格式。
 * Input: rel，表关系。
 *        rte，关系的 rangetable 条目。
 * Output: 无。
 * Return Value: 无。
 * Notes: 1. 如果 Dfs 表是 CU 格式，标记为 REL_COL_ORIENTED，
 *            否则标记为 REL_PAX_ORIENTED。
 */
static void setRteOrientation(Relation rel, RangeTblEntry* rte)
{
    if (RelationIsCUFormat(rel)) {
        rte->orientation = REL_COL_ORIENTED;
#ifdef ENABLE_MULTIPLE_NODES
    } else if (RelationIsPAXFormat(rel)) {
        rte->orientation = REL_PAX_ORIENTED;

        /* 如果仅对 HDFS 表进行分析，确保用户只能获取 HDFS 上的数据。 */
        if (!u_sess->analyze_cxt.is_under_analyze) {
            /* 禁止用户仅在 HDFS 上获取数据。 */
            rte->inh = true;
        }
    } else if (RelationIsTsStore(rel)) {
        rte->orientation = REL_TIMESERIES_ORIENTED;
#endif
    } else {
        rte->orientation = REL_ROW_ORIENTED;
    }
}

/* 检查表中的索引，混合使用强制和使用 */
static IndexHintType preCheckIndexHints(ParseState* pstate, List* indexhints, Relation relation)
{
    IndexHintType retType = INDEX_HINT_USE;
    ListCell* lc = NULL;
    ListCell* lc_index = NULL;
    List* indexOidList = NIL;
    Oid indexOid = InvalidOid;
    Oid relationOid = RelationGetRelid(relation);
    Oid relationNsOid = RelationGetNamespace(relation);
    List* indexList = RelationGetIndexList(relation);
    IndexHintDefinition* idef = NULL;
    bool exist_indexs = false;

    /* 表中没有索引，返回 */
    if (indexList == NIL) {
        retType = INDEX_HINT_NOT_EXISTS;
        return retType;
    }

    IndexHintType itype = ((IndexHintDefinition*)lfirst(list_head(indexhints)))->index_type;
    foreach (lc, indexhints) {
        idef = (IndexHintDefinition*)lfirst(lc);
        itype = (IndexHintType)(idef->index_type | itype);
        if (itype == INDEX_HINT_MIX) {
            retType = INDEX_HINT_MIX;
            goto err;
        }
        /* 检查索引是否在表中 */
        foreach (lc_index, idef->indexnames) {
            indexOid = get_relname_relid(strVal(lfirst(lc_index)), relationNsOid);
            exist_indexs = false;
            if (OidIsValid(indexOid)) {
                if (list_member_oid(indexList, indexOid)) {
                    exist_indexs = true;
                }
            }
            if (!exist_indexs) {
                retType = INDEX_HINT_NOT_EXISTS;
                goto err;
            }
            IndexHintRelationData* indexdata = makeNode(IndexHintRelationData);
            indexdata->indexOid = indexOid;
            indexdata->relationOid = relationOid;
            indexdata->index_type = idef->index_type;
            indexOidList = list_append_unique(indexOidList, (Node*)indexdata);
        }
    }
    pstate->p_indexhintLists = list_copy(indexOidList);
err:
    if (indexOidList != NIL)
        list_free(indexOidList);
    return retType;
}


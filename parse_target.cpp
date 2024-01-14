/* -------------------------------------------------------------------------
 *
 * parse_target.cpp
 *	  handle target lists
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/common/backend/parser/parse_target.cpp
 *
 * -------------------------------------------------------------------------
 */
#include "postgres.h"
#include "knl/knl_variable.h"

#include "catalog/pg_type.h"
#include "commands/dbcommands.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "parser/parsetree.h"
#include "parser/parse_coerce.h"
#include "parser/parse_expr.h"
#include "parser/parse_func.h"
#include "parser/parse_relation.h"
#include "parser/parse_target.h"
#include "parser/parse_type.h"
#include "parser/parse_collate.h"
#include "nodes/parsenodes_common.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "utils/rel_gs.h"
#include "utils/typcache.h"
#include "executor/executor.h"
#include "gs_ledger/ledger_utils.h"
#include "mb/pg_wchar.h"
#include "parser/parse_utilcmd.h"

static void markTargetListOrigin(ParseState* pstate, TargetEntry* tle, Var* var, int levelsup);
static Node* transformAssignmentIndirection(ParseState* pstate, Node* basenode, const char* targetName,
    bool targetIsArray, Oid targetTypeId, int32 targetTypMod, Oid targetCollation, ListCell* indirection, Node* rhs,
    int location);
static Node* transformAssignmentSubscripts(ParseState* pstate, Node* basenode, const char* targetName, Oid targetTypeId,
    int32 targetTypMod, Oid targetCollation, List* subscripts, bool isSlice, ListCell* next_indirection, Node* rhs,
    int location);
static List* ExpandColumnRefStar(ParseState* pstate, ColumnRef* cref, bool targetlist);
static List* ExpandAllTables(ParseState* pstate, int location);
static List* ExpandIndirectionStar(ParseState* pstate, A_Indirection* ind, bool targetlist, ParseExprKind exprKind);
static List* ExpandSingleTable(ParseState* pstate, RangeTblEntry* rte, int location, bool targetlist);
static List* ExpandRowReference(ParseState* pstate, Node* expr, bool targetlist);
static int FigureColnameInternal(Node* node, char** name);

/*
 * @Description: 返回最后一个字段的名称，忽略 "*" 或下标
 * @in field: 要搜索的字段列表
 * @return 找到的字段的名称
 */
static char* find_last_field_name(List* field)
{
    char* fname = NULL;
    ListCell* l = NULL;
    Node* i = NULL;
    /* 查找最后一个字段的名称，如果有的话，忽略 "*" 和下标 */
    foreach (l, field) {
        i = (Node*)lfirst(l);
        if (IsA(i, String)) {
            fname = strVal(i);
        }
    }
    return fname;
}

/*
 * transformTargetEntry()
 * 将任何普通的“表达式类型”节点转换为目标列表条目。
 * 导出此函数以便 parse_clause.c 可以为 ORDER/GROUP BY 项生成目标列表条目，
 * 这些项尚未在目标列表中。
 *
 * node		值表达式的（未转换的）解析树
 * expr		转换后的表达式，如果调用者尚未完成转换则为NULL。
 * colname	要分配的列名，如果尚未设置则为NULL。
 * resjunk	true表示目标应标记为 resjunk，即在最终的投影元组中不需要。
 */
TargetEntry* transformTargetEntry(ParseState* pstate, Node* node, Node* expr, ParseExprKind exprKind, char* colname, bool resjunk)
{
    /* 为错误情况生成适当的列名 */
    if (colname == NULL && !resjunk) {
        colname = FigureIndexColname(node);
    }
    ELOG_FIELD_NAME_START(colname);

    /* 如果调用者尚未转换节点，则转换节点 */
    if (expr == NULL) {
        expr = transformExpr(pstate, node, exprKind);
    }
    ELOG_FIELD_NAME_END;

    if (colname == NULL && !resjunk) {
        /*
         * 为没有任何显式 'AS 列名' 子句的列生成一个适当的列名，
         * 可能由于节点表达式的更改而与上述调用不同
         */
        colname = FigureColname(node);
    }

    return makeTargetEntry((Expr*)expr, (AttrNumber)pstate->p_next_resno++, colname, resjunk);
}

/*
 * transformTargetList()
 * 将 ResTarget 列表转换为 TargetEntry 列表。
 *
 * 在这一点上，我们不关心是进行 SELECT、INSERT 还是 UPDATE；我们只是转换给定的表达式（“val”字段）。
 */
List* transformTargetList(ParseState* pstate, List* targetlist, ParseExprKind exprKind)
{
    List* p_target = NIL;
    ListCell* o_target = NULL;

    foreach (o_target, targetlist) {
        ResTarget* res = (ResTarget*)lfirst(o_target);

        /*
         * 检查是否为 "something.*"。根据 "something" 的复杂性，
         * 星号可能出现在 ColumnRef 中的最后一个字段，或者在 A_Indirection 中的最后一个间接项中。
         */
        if (IsA(res->val, ColumnRef)) {
            ColumnRef* cref = (ColumnRef*)res->val;

            if (cref->prior) {
                ereport(ERROR,
                        (errcode(ERRCODE_OPTIMIZER_INCONSISTENT_STATE),
                         errmsg("在 TargetList 中不支持 prior 列。")));
            }

            if (IsA(llast(cref->fields), A_Star)) {
                /* 是 something.*，展开为多个项 */
                p_target = list_concat(p_target, ExpandColumnRefStar(pstate, cref, true));
                continue;
            }
        } else if (IsA(res->val, A_Indirection)) {
            A_Indirection* ind = (A_Indirection*)res->val;

            if (IsA(llast(ind->indirection), A_Star)) {
                /* 是 something.*，展开为多个项 */
                p_target = list_concat(p_target, ExpandIndirectionStar(pstate, ind, true, exprKind));
                continue;
            }
        }

        /*
         * 不是 "something.*"，因此将其作为单个表达式转换
         */
        p_target = lappend(p_target, transformTargetEntry(pstate, res->val, NULL, exprKind, res->name, false));
        pstate->p_target_list = p_target;
    }

    return p_target;
}

/*
 * transformExpressionList()
 *
 * 这与 transformTargetList 的转换相同，只是输入列表元素是没有 ResTarget 装饰的纯表达式，
 * 输出元素也是没有 TargetEntry 装饰的纯表达式。我们在 ROW() 和 VALUES() 构造中使用这个。
 */
List* transformExpressionList(ParseState* pstate, List* exprlist, ParseExprKind exprKind)
{
    List* result = NIL;
    ListCell* lc = NULL;

    foreach (lc, exprlist) {
        Node* e = (Node*)lfirst(lc);

        /*
         * 检查是否为 "something.*"。根据 "something" 的复杂性，
         * 星号可能出现在 ColumnRef 中的最后一个字段，或者在 A_Indirection 中的最后一个间接项中。
         */
        if (IsA(e, ColumnRef)) {
            ColumnRef* cref = (ColumnRef*)e;

            if (IsA(llast(cref->fields), A_Star)) {
                /* 是 something.*，展开为多个项 */
                result = list_concat(result, ExpandColumnRefStar(pstate, cref, false));
                continue;
            }
        } else if (IsA(e, A_Indirection)) {
            A_Indirection* ind = (A_Indirection*)e;

            if (IsA(llast(ind->indirection), A_Star)) {
                /* 是 something.*，展开为多个项 */
                result = list_concat(result, ExpandIndirectionStar(pstate, ind, false, exprKind));
                continue;
            }
        }

        /*
         * 不是 "something.*"，因此将其作为单个表达式转换
         */
        result = lappend(result, transformExpr(pstate, e, exprKind));
    }

    return result;
}

/*
 * resolveTargetListUnknowns()
 * 将任何未知类型的 targetlist 条目转换为 TEXT 类型。
 *
 * 在我们耗尽了查询的所有其他识别输出列类型的方法后，我们执行此操作。
 */
void resolveTargetListUnknowns(ParseState* pstate, List* targetlist)
{
    ListCell* l = NULL;

    foreach (l, targetlist) {
        TargetEntry* tle = (TargetEntry*)lfirst(l);
        Oid restype = exprType((Node*)tle->expr);
        if (UNKNOWNOID == restype) {
            tle->expr = (Expr*)coerce_type(
                pstate, (Node*)tle->expr, restype, TEXTOID, -1, COERCION_IMPLICIT, COERCE_IMPLICIT_CAST, -1);
        }
    }
}

/*
 * markTargetListOrigins()
 * 标记具有源表的OID和列编号的简单Var的目标列表列
 *
 * 目前，仅对SELECT目标列表执行此操作，因为只有在我们将其发送到前端时才需要这些信息。
 */
void markTargetListOrigins(ParseState* pstate, List* targetlist)
{
    ListCell* l = NULL;

    foreach (l, targetlist) {
        TargetEntry* tle = (TargetEntry*)lfirst(l);

        markTargetListOrigin(pstate, tle, (Var*)tle->expr, 0);
    }
}

/*
 * markTargetListOrigin()
 * 如果 'var' 是普通关系的Var，则使用其源标记 'tle'
 *
 * levelsup 是一个额外的偏移量，以正确解释Var的varlevelsup。
 *
 * 将此分为递归引用的连接引用，以便递归。注意我们不深入视图，而是将视图报告为列所有者。
 */
static void markTargetListOrigin(ParseState* pstate, TargetEntry* tle, Var* var, int levelsup)
{
    int netlevelsup;
    RangeTblEntry* rte = NULL;
    AttrNumber attnum;

    if (var == NULL || !IsA(var, Var)) {
        return;
    }
    netlevelsup = var->varlevelsup + levelsup;
    rte = GetRTEByRangeTablePosn(pstate, var->varno, netlevelsup);
    attnum = var->varattno;

    switch (rte->rtekind) {
        case RTE_RELATION:
            /* 是表或视图，报告它 */
            tle->resorigtbl = rte->relid;
            tle->resorigcol = attnum;
            break;
        case RTE_SUBQUERY:
            /* FROM子句中的子查询：从子查询中复制上来 */
            if (attnum != InvalidAttrNumber) {
                TargetEntry* ste = get_tle_by_resno(rte->subquery->targetList, attnum);

                if (ste == NULL || ste->resjunk) {
                    ereport(ERROR,
                        (errcode(ERRCODE_OPTIMIZER_INCONSISTENT_STATE),
                            errmsg("子查询 %s 不包含属性 %d", rte->eref->aliasname, attnum)));
                }
                tle->resorigtbl = ste->resorigtbl;
                tle->resorigcol = ste->resorigcol;
            }
            break;
        case RTE_JOIN:
            /* 连接RTE --- 递归检查别名变量 */
            if (attnum != InvalidAttrNumber) {
                Var* aliasvar = NULL;

                AssertEreport(attnum > 0, MOD_OPT, "");
                AssertEreport(attnum <= list_length(rte->joinaliasvars), MOD_OPT, "");
                aliasvar = (Var*)list_nth(rte->joinaliasvars, attnum - 1);
                markTargetListOrigin(pstate, tle, aliasvar, netlevelsup);
            }
            break;
        case RTE_FUNCTION:
        case RTE_VALUES:
        case RTE_RESULT:
            /* 不是简单关系，不进行标记 */
            break;
        case RTE_CTE:

            /*
             * CTE引用：从子查询中复制上来，如果可能的话。
             * 如果RTE是递归自引用，则我们不能做任何事情，因为我们尚未完成对其的分析。
             * 但是，这不是什么大问题，因为我们必须在递归CTE的递归术语中，所以
             * 目前的目标列表上的任何标记都不会影响结果。
             */
            if (attnum != InvalidAttrNumber && !rte->self_reference) {
                CommonTableExpr* cte = GetCTEForRTE(pstate, rte, netlevelsup);
                TargetEntry* ste = NULL;

                ste = get_tle_by_resno(GetCTETargetList(cte), attnum);
                if (ste == NULL || ste->resjunk) {
                    ereport(ERROR,
                        (errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
                            errmsg("子查询 %s 不包含属性 %d", rte->eref->aliasname, attnum)));
                }
                tle->resorigtbl = ste->resorigtbl;
                tle->resorigcol = ste->resorigcol;
            }
            break;
#ifdef PGXC
        case RTE_REMOTE_DUMMY:
            ereport(ERROR, (errcode(ERRCODE_INVALID_OPERATION), errmsg("发现无效的RTE")));
            break;
#endif /* PGXC */
        default:
            break;
    }
}

/*
 * transformAssignedExpr()
 * 该函数仅在 INSERT 和 UPDATE（包括 DUPLICATE KEY UPDATE）语句中使用。
 * 用于准备一个表达式，将值分配给目标表的列。这包括将给定值强制转换为目标列的类型（如果需要），
 * 以及处理附加到目标列本身的任何子字段名称或下标。输入表达式已经通过 transformExpr() 处理。
 *
 * 参数：
 *   pstate      - 解析状态
 *   expr        - 待修改的表达式
 *   exprKind    - 表达式类型
 *   colname     - 目标列名称（即要分配给的属性名称）
 *   attrno      - 目标属性编号
 *   indirection - 目标列的下标/字段名，如果有的话
 *   location    - 错误光标位置，或 -1
 *   rd          - 关系描述符
 *   rte         - 范围表条目
 *
 * 返回修改后的表达式。
 *
 * 注意：location 指向目标列名称（SET 目标或 INSERT 列名列表项），因此在省略列名列表的 INSERT 中，它通常应为 -1。
 * 因此，对于可能发生在默认 INSERT 中的错误，我们通常更喜欢使用 exprLocation(expr)。
 */
Expr* transformAssignedExpr(ParseState* pstate, Expr* expr, ParseExprKind exprKind, char* colname, int attrno,
                            List* indirection, int location, Relation rd, RangeTblEntry* rte)
{
    Oid type_id;    /* 提供的值的类型 */
    int32 type_mod; /* 提供的值的 typmod */
    Oid attrtype;   /* 目标列的类型 */
    int32 attrtypmod;
    Oid attrcollation; /* 目标列的排序规则 */
    int attrcharset = PG_INVALID_ENCODING;
    ParseExprKind sv_expr_kind;

    /*
    * 保存和恢复正在解析的表达式类型的标识。
    * 我们必须在这里设置 p_expr_kind，因为可以在不通过 transformExpr() 的情况下解析下标。
    */
    Assert(exprKind != EXPR_KIND_NONE);
    sv_expr_kind = pstate->p_expr_kind;
    pstate->p_expr_kind = exprKind;

    AssertEreport(rd != NULL, MOD_OPT, "");
    /*
     * 对于不在分类账模式中的关系，只有 attrno 是系统列，
     * 对于分类账模式中的关系，“hash”列被保留为系统列。
     * 对于分类账模式中表的“hash”列，我们禁止插入和更新。
     */
    bool is_system_column = (attrno <= 0 || (rd->rd_isblockchain && strcmp(colname, "hash") == 0));
    if (is_system_column) {
        ereport(ERROR,
            (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                errmsg("cannot assign to system column \"%s\"", colname),
                parser_errposition(pstate, location)));
    }
    attrtype = attnumTypeId(rd, attrno);
    attrtypmod = rd->rd_att->attrs[attrno - 1].atttypmod;
    attrcollation = rd->rd_att->attrs[attrno - 1].attcollation;
    if (DB_IS_CMPT(B_FORMAT) && OidIsValid(attrcollation)) {
        attrcharset = get_valid_charset_by_collation(attrcollation);
    }

    /*
     * 如果表达式是一个 DEFAULT 占位符，则将属性的类型/typmod/排序规则插入其中，
     * 以便 exprType 等能够报告正确的内容。
     * （我们期望最终替换的默认表达式实际上具有这种类型和 typmod。
     * 排序规则可能无关紧要，但我们仍然正确设置它。）
     * 同时，拒绝使用 DEFAULT 更新子字段或数组元素，因为列的部分不可能有默认值。
     */
    if (expr && IsA(expr, SetToDefault)) {
        SetToDefault* def = (SetToDefault*)expr;

        def->typeId = attrtype;
        def->typeMod = attrtypmod;
        def->collation = attrcollation;
        if (indirection != NULL) {
            if (IsA(linitial(indirection), A_Indices)) {
                ereport(ERROR,
                    (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("cannot set an array element to DEFAULT"),
                        parser_errposition(pstate, location)));
            } else {
                ereport(ERROR,
                    (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("cannot set a subfield to DEFAULT"),
                        parser_errposition(pstate, location)));
            }
        }
    }

    /* 现在我们可以安全使用 exprType()。*/
    type_id = exprType((Node*)expr);
    type_mod = exprTypmod((Node*)expr);

    ELOG_FIELD_NAME_START(colname);

    /*
     * 如果目标列上有下标，则准备一个数组或子字段赋值表达式。
     * 这将生成一个新的列值，将源值插入其中，然后可以将其放置在由 INSERT 或 UPDATE 构造的新元组中。
     */
    if (indirection != NULL) {
        Node* colVar = NULL;

        if (pstate->p_is_insert) {
            /*
             * 命令是 INSERT INTO table (col.something) ... 所以实际上没有源值可用。
             * 将 NULL 常量插入作为源值。
             */
            colVar = (Node*)makeNullConst(attrtype, attrtypmod, attrcollation);
        } else {
            /*
             * 为要更新的列构建一个 Var。
             */
            colVar = (Node*)make_var(pstate, rte, attrno, location);
        }

        expr = (Expr*)transformAssignmentIndirection(pstate,
            colVar,
            colname,
            false,
            attrtype,
            attrtypmod,
            attrcollation,
            list_head(indirection),
            (Node*)expr,
            location);
    } else {
        /*
         * 对于正常的非限定目标列，进行类型检查和强制转换。
         */
        Node* orig_expr = (Node*)expr;

        /*
         * 对于 insert 语句，我们可能会进行自动截断。
         * 当：
         * (1) p_is_td_compatible_truncation 为 true;
         * (2) 目标列类型为 char 和 varchar 类型;
         * (3) 目标列长度小于源列长度;
         * 		a) type_mod <= 0，因为源可能是常量，那么我们都添加强制转换
         * 		b) 源列长度和目标列长度都存在，那么当目标长度小于源长度时，我们只添加显式转换
         * 都满足。然后我们将为源列数据添加显式转换，以便成功插入目标列。
         * 不支持 nvarchar2 类型自动截断。
         */
        bool is_all_satisfied = pstate->p_is_td_compatible_truncation &&
            (attrtype == BPCHAROID || attrtype == VARCHAROID) &&
            ((type_mod > 0 && attrtypmod < type_mod) || type_mod < 0);

        if (type_is_set(attrtype)) {
            Node* orig_expr = (Node*)expr;
            expr = (Expr*)coerce_to_settype(
                    pstate, orig_expr, type_id, attrtype, attrtypmod, COERCION_ASSIGNMENT, COERCE_IMPLICIT_CAST, -1, attrcollation);
        } else if (is_all_satisfied) {
            expr = (Expr*)coerce_to_target_type(
                pstate, orig_expr, type_id, attrtype, attrtypmod, COERCION_ASSIGNMENT, COERCE_EXPLICIT_CAST, -1);
            pstate->tdTruncCastStatus = TRUNC_CAST_QUERY;
        } else {
            expr = (Expr*)coerce_to_target_type(
                pstate, orig_expr, type_id, attrtype, attrtypmod, COERCION_ASSIGNMENT, COERCE_IMPLICIT_CAST, -1);
        }
        if (expr == NULL) {
            /* 如果我们在创建过程中 - 更改输入参数类型 */
            if (IsClientLogicType(attrtype) && IsA(orig_expr, Param) && pstate->p_create_proc_insert_hook != NULL) {
                int param_no = ((Param*)orig_expr)->paramid - 1;
                pstate->p_create_proc_insert_hook(pstate, param_no, attrtype, RelationGetRelid(rd), colname);
                type_id = attrtype;
                expr = (Expr*)coerce_to_target_type(pstate, orig_expr, type_id, attrtype, attrtypmod,
                    COERCION_ASSIGNMENT, COERCE_IMPLICIT_CAST, -1);
            }
        }
        if (expr == NULL) {
            bool invalid_encrypted_column = 
                ((attrtype == BYTEAWITHOUTORDERWITHEQUALCOLOID || attrtype == BYTEAWITHOUTORDERCOLOID) &&
                coerce_to_target_type(pstate, orig_expr, type_id, attrtypmod, -1, COERCION_ASSIGNMENT,
                    COERCE_IMPLICIT_CAST, -1));
            if (invalid_encrypted_column) {
                ereport(ERROR, (errcode(ERRCODE_INVALID_ENCRYPTED_COLUMN_DATA),
                    errmsg("column \"%s\" is of type %s"
                    " but expression is of type %s",
                    colname, format_type_be(attrtype), format_type_be(type_id)),
                    errhint("You will need to rewrite or cast the expression."),
                    parser_errposition(pstate, exprLocation(orig_expr))));
            } else {
                if (!pstate->p_has_ignore) {
                    ereport(ERROR, (errcode(ERRCODE_DATATYPE_MISMATCH),
                        errmsg("column \"%s\" is of type %s"
                               " but expression is of type %s",
                               colname, format_type_be(attrtype), format_type_be(type_id)),
                               errhint("You will need to rewrite or cast the expression."),
                               parser_errposition(pstate, exprLocation(orig_expr))));
                }
                expr = (Expr*)makeConst(attrtype, attrtypmod, attrcollation, rd->rd_att->attrs[attrno - 1].attlen,
                                        GetTypeZeroValue(&rd->rd_att->attrs[attrno - 1]), false,
                                        rd->rd_att->attrs[attrno - 1].attbyval);
                ereport(WARNING, (errcode(ERRCODE_DATATYPE_MISMATCH),
                                errmsg("column \"%s\" is of type %s"
                                       " but expression is of type %s. Data truncated automatically.",
                                       colname, format_type_be(attrtype), format_type_be(type_id))));
            }
        }
    }
#ifndef ENABLE_MULTIPLE_NODES
    if (attrcharset != PG_INVALID_ENCODING) {
        assign_expr_collations(pstate, (Node*)expr);
        expr = (Expr*)coerce_to_target_charset((Node*)expr, attrcharset, attrtype, attrtypmod, attrcollation);
    }
#endif

    ELOG_FIELD_NAME_END;

    pstate->p_expr_kind = sv_expr_kind;

    return expr;
}

/*
 * updateTargetListEntry()
 * 该函数仅在UPDATE（包括DUPLICATE KEY UPDATE）语句中使用。
 * 它准备一个UPDATE TargetEntry，用于分配给目标表的列。这包括将给定的值强制转换为目标列的类型（如果需要），
 * 以及处理附加到目标列本身的任何子字段名或下标。
 *
 * pstate        解析状态
 * tle           要修改的目标列表条目
 * colname       目标列名称（即要分配给的属性名称）
 * attrno        目标属性编号
 * indirection   目标列的下标或字段名列表
 * location      错误光标位置（应指向列名），或-1
 */
void updateTargetListEntry(ParseState* pstate, TargetEntry* tle, char* colname, int attrno,
    List* indirection, int location, Relation rd, RangeTblEntry* rte)
{
    /* 根据需要修复表达式 */
    tle->expr = transformAssignedExpr(pstate, tle->expr, EXPR_KIND_UPDATE_TARGET, colname, attrno,
                                      indirection, location, rd, rte);

    /*
     * 设置resno以标识目标列 --- 重写器和规划器依赖于此。我们还设置了resname以标识目标列，但这仅用于调试目的；
     * 不应依赖于它（特别是在存储的规则中可能过时的情况下）。
     */
    tle->resno = (AttrNumber)attrno;
    tle->resname = colname;
}

/*
 * 处理INSERT/UPDATE中目标列的指向（字段选择或下标）。
 * 该函数对多个级别的指向进行递归调用，但请注意，指向列表中的几个相邻的A_Indices节点将被视为单个多维下标操作。
 *
 * 在初始调用中，basenode是UPDATE中目标列的Var，或者在INSERT中是目标类型的null Const。在递归调用中，basenode为NULL，
 * 表示如果需要，应该构造一个替代节点。
 *
 * targetName是我们正在分配的字段或子字段的名称，targetIsArray为true表示我们正在对其进行下标操作。
 * 这些仅用于错误报告。
 *
 * targetTypeId，targetTypMod，targetCollation指示要分配给的对象的数据类型和排序规则
 * （最初是目标列，稍后是某个子对象）。
 *
 * indirection是要处理的剩余子列表。当为NULL时，我们已经递归完成，只需强制转换并返回RHS。
 *
 * rhs是已经转换的要分配的值；请注意，它尚未被强制转换为任何特定类型。
 *
 * location是错误的光标位置。（注意：这指向目标子句的头部，例如在“foo.bar[baz]”中，“foo”是“baz”。稍后我们可能想要使用
 * 自己的位置信息装饰指向单元格，在这种情况下，位置参数可能会被省略。）
 */
static Node* transformAssignmentIndirection(ParseState* pstate, Node* basenode, const char* targetName,
    bool targetIsArray, Oid targetTypeId, int32 targetTypMod, Oid targetCollation, ListCell* indirection, Node* rhs,
    int location)
{
    Node* result = NULL;
    List* subscripts = NIL;
    bool isSlice = false;
    ListCell* i = NULL;

    if (indirection != NULL && basenode == NULL) {
        /* 设置替代。我们重用CaseTestExpr。*/
        CaseTestExpr* ctest = makeNode(CaseTestExpr);

        ctest->typeId = targetTypeId;
        ctest->typeMod = targetTypMod;
        ctest->collation = targetCollation;
        basenode = (Node*)ctest;
    }

    /*
     * 我们必须将字段选择操作与下标操作分开。必须将相邻的A_Indices节点视为单个多维下标操作。
     */
    for_each_cell(i, indirection)
    {
        Node* n = (Node*)lfirst(i);

        if (IsA(n, A_Indices)) {
            subscripts = lappend(subscripts, n);
            if (((A_Indices*)n)->lidx != NULL) {
                isSlice = true;
            }
        } else if (IsA(n, A_Star)) {
            ereport(ERROR,
                (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                    errmsg("row expansion via \"*\" is not supported here"),
                    parser_errposition(pstate, location)));
        } else {
            FieldStore* fstore = NULL;
            Oid typrelid;
            AttrNumber attnum;
            Oid fieldTypeId;
            int32 fieldTypMod;
            Oid fieldCollation;

            AssertEreport(IsA(n, String), MOD_OPT, "");

            /* 在处理此字段选择之前处理下标 */
            if (subscripts != NULL) {
                /* 递归，然后返回，因为我们已经完成了 */
                return transformAssignmentSubscripts(pstate,
                    basenode,
                    targetName,
                    targetTypeId,
                    targetTypMod,
                    targetCollation,
                    subscripts,
                    isSlice,
                    i,
                    rhs,
                    location);
            }

            /* 没有下标，因此可以在此处处理字段选择 */
            typrelid = typeidTypeRelid(targetTypeId);
            if (!typrelid) {
                ereport(ERROR,
                    (errcode(ERRCODE_DATATYPE_MISMATCH),
                        errmsg("cannot assign to field \"%s\" of column \"%s\" because its type %s is not a composite "
                               "type",
                            strVal(n),
                            targetName,
                            format_type_be(targetTypeId)),
                        parser_errposition(pstate, location)));
            }

            attnum = get_attnum(typrelid, strVal(n));
            if (attnum == InvalidAttrNumber) {
                ereport(ERROR,
                    (errcode(ERRCODE_UNDEFINED_COLUMN),
                        errmsg("cannot assign to field \"%s\" of column \"%s\" because there is no such column in data "
                               "type %s",
                            strVal(n),
                            targetName,
                            format_type_be(targetTypeId)),
                        parser_errposition(pstate, location)));
            }
            if (attnum < 0) {
                ereport(ERROR,
                    (errcode(ERRCODE_UNDEFINED_COLUMN),
                        errmsg("cannot assign to system column \"%s\"", strVal(n)),
                        parser_errposition(pstate, location)));
            }
            /* 对于ledger模式中表的“hash”列，我们禁止插入和更新 */
            if (strcmp(strVal(n), "hash") == 0 && is_ledger_usertable(typrelid)) {
                ereport(ERROR,
                    (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("cannot assign to system column \"%s\"", strVal(n)),
                        parser_errposition(pstate, location)));
            }
            get_atttypetypmodcoll(typrelid, attnum, &fieldTypeId, &fieldTypMod, &fieldCollation);

            /* 递归以为字段分配创建适当的RHS */
            rhs = transformAssignmentIndirection(
                pstate, NULL, strVal(n), false, fieldTypeId, fieldTypMod, fieldCollation, lnext(i), rhs, location);

            /* 并构建FieldStore节点 */
            fstore = makeNode(FieldStore);
            fstore->arg = (Expr*)basenode;
            fstore->newvals = list_make1(rhs);
            fstore->fieldnums = list_make1_int(attnum);
            fstore->resulttype = targetTypeId;

            return (Node*)fstore;
        }
    }

    /* 处理尾随的下标，如果有的话 */
    if (subscripts != NULL) {
        /* 递归，然后返回，因为我们已经完成了 */
        return transformAssignmentSubscripts(pstate,
            basenode,
            targetName,
            targetTypeId,
            targetTypMod,
            targetCollation,
            subscripts,
            isSlice,
            NULL,
            rhs,
            location);
    }

    /* 基本情况：只需将RHS强制转换为匹配的目标类型ID */
    result = coerce_to_target_type(
        pstate, rhs, exprType(rhs), targetTypeId, targetTypMod, COERCION_ASSIGNMENT, COERCE_IMPLICIT_CAST, -1);
    if (result == NULL) {
        if (targetIsArray) {
            ereport(ERROR,
                (errcode(ERRCODE_DATATYPE_MISMATCH),
                    errmsg("array assignment to \"%s\" requires type %s"
                           " but expression is of type %s",
                        targetName,
                        format_type_be(targetTypeId),
                        format_type_be(exprType(rhs))),
                    errhint("You will need to rewrite or cast the expression."),
                    parser_errposition(pstate, location)));
        } else {
            ereport(ERROR,
                (errcode(ERRCODE_DATATYPE_MISMATCH),
                    errmsg("subfield \"%s\" is of type %s"
                           " but expression is of type %s",
                        targetName,
                        format_type_be(targetTypeId),
                        format_type_be(exprType(rhs))),
                    errhint("You will need to rewrite or cast the expression."),
                    parser_errposition(pstate, location)));
        }
    }

    return result;
}

/*
 * helper for transformAssignmentIndirection: process array assignment
 */
static Node* transformAssignmentSubscripts(ParseState* pstate, Node* basenode, const char* targetName, Oid targetTypeId,
    int32 targetTypMod, Oid targetCollation, List* subscripts, bool isSlice, ListCell* next_indirection, Node* rhs,
    int location)
{
    Node* result = NULL;
    Oid arrayType;
    int32 arrayTypMod;
    Oid elementTypeId;
    Oid typeNeeded;
    Oid collationNeeded;

    AssertEreport(subscripts != NIL, MOD_OPT, "");

    /* 确定涉及的实际数组类型和元素类型 */
    arrayType = targetTypeId;
    arrayTypMod = targetTypMod;
    elementTypeId = transformArrayType(&arrayType, &arrayTypMod);

    /* 确定 RHS 必须提供的类型 */
    typeNeeded = isSlice ? arrayType : elementTypeId;

    /*
     * 数组通常与元素具有相同的排序，但有一个例外：我们可能正在对数组类型上的域进行下标。在这种情况下，使用基本类型的排序。
     */
    if (arrayType == targetTypeId) {
        collationNeeded = targetCollation;
    } else {
        collationNeeded = get_typcollation(arrayType);
    }
    /* 递归以为数组赋值创建适当的 RHS */
    rhs = transformAssignmentIndirection(
        pstate, NULL, targetName, true, typeNeeded, arrayTypMod, collationNeeded, next_indirection, rhs, location);

    /* 处理下标 */
    result = (Node*)transformArraySubscripts(pstate, basenode, arrayType, elementTypeId, arrayTypMod, subscripts, rhs);

    /* 如果目标是数组上的域，则需要强制转换到域 */
    if (arrayType != targetTypeId) {
        result = coerce_to_target_type(pstate,
            result,
            exprType(result),
            targetTypeId,
            targetTypMod,
            COERCION_ASSIGNMENT,
            COERCE_IMPLICIT_CAST,
            -1);
        /* 可能不应该失败，但检查一下 */
        if (result == NULL) {
            ereport(ERROR,
                (errcode(ERRCODE_CANNOT_COERCE),
                    errmsg("cannot cast type %s to %s", format_type_be(exprType(result)), format_type_be(targetTypeId)),
                    parser_errposition(pstate, location)));
        }
    }

    return result;
}

/*
 * checkInsertTargets -
 *	  generate a list of INSERT column targets if not supplied, or
 *	  test supplied column names to make sure they are in target table.
 *	  Also return an integer list of the columns' attribute numbers.
 */
List* checkInsertTargets(ParseState* pstate, List* cols, List** attrnos)
{
    *attrnos = NIL;
    bool is_blockchain_rel = false;
    Relation targetrel = (Relation)linitial(pstate->p_target_relation);

    if (cols == NIL) {
        /*
         * 为 INSERT 生成默认的列列表。
         */
        if (targetrel == NULL) {
            ereport(ERROR,
                (errmodule(MOD_OPT),
                    errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED),
                    errmsg("targetrel is NULL unexpectedly")));
        }

        FormData_pg_attribute* attr = targetrel->rd_att->attrs;
        int numcol = RelationGetNumberOfAttributes(targetrel);
        int i;
        is_blockchain_rel = targetrel->rd_isblockchain;

        for (i = 0; i < numcol; i++) {
            ResTarget* col = NULL;

            if (attr[i].attisdropped) {
                continue;
            }
            /* 如果时间序列关系中的隐藏列，请跳过它 */
            if (TsRelWithImplDistColumn(attr, i) && RelationIsTsStore(targetrel)) {
                continue;
            }

            col = makeNode(ResTarget);
            col->name = pstrdup(NameStr(attr[i].attname));
            if (is_blockchain_rel && strcmp(col->name, "hash") == 0) {
                continue;
            }
            col->indirection = NIL;
            col->val = NULL;
            col->location = -1;
            cols = lappend(cols, col);
            *attrnos = lappend_int(*attrnos, i + 1);
        }
    } else {
        /*
         * 进行用户提供的 INSERT 列表的初始验证。
         */
        Bitmapset* wholecols = NULL;
        Bitmapset* partialcols = NULL;
        ListCell* tl = NULL;

        foreach (tl, cols) {
            ResTarget* col = (ResTarget*)lfirst(tl);
            char* name = col->name;
            int attrno;

            /* 查找列名，失败则报告错误 */
            attrno = attnameAttNum(targetrel, name, false);
            if (attrno == InvalidAttrNumber) {
                ereport(ERROR,
                    (errcode(ERRCODE_UNDEFINED_COLUMN),
                        errmsg("column \"%s\" of relation \"%s\" does not exist",
                            name,
                            RelationGetRelationName(targetrel)),
                        parser_errposition(pstate, col->location)));
            }
            /*
             * 检查重复项，但仅限于整个列 --- 我们允许 INSERT INTO foo (col.subcol1, col.subcol2)
             */
            if (col->indirection == NIL) {
                /* 整列；不能有其他赋值 */
                if (bms_is_member(attrno, wholecols) || bms_is_member(attrno, partialcols)) {
                    ereport(ERROR,
                        (errcode(ERRCODE_DUPLICATE_COLUMN),
                            errmsg("column \"%s\" specified more than once", name),
                            parser_errposition(pstate, col->location)));
                }
                wholecols = bms_add_member(wholecols, attrno);
            } else {
                /* 部分列；不能有整列赋值 */
                if (bms_is_member(attrno, wholecols)) {
                    ereport(ERROR,
                        (errcode(ERRCODE_DUPLICATE_COLUMN),
                            errmsg("column \"%s\" specified more than once", name),
                            parser_errposition(pstate, col->location)));
                }
                partialcols = bms_add_member(partialcols, attrno);
            }

            *attrnos = lappend_int(*attrnos, attrno);
        }
    }

    return cols;
}

/*
 * ExpandColumnRefStar()
 *		将 foo.* 转换为表达式列表或目标列表条目。
 *
 * 这处理了星号(*)出现在ColumnRef的最后或仅成员的情况。
 * 该代码用于处理星号引用在SELECT目标列表的顶层（其中我们希望在结果中得到TargetEntry节点）
 * 以及星号引用在ROW()或VALUES()结构中的情况（其中我们只希望得到裸露的表达式）。
 *
 * 被引用的列被标记为需要SELECT访问。
 */
static List* ExpandColumnRefStar(ParseState* pstate, ColumnRef* cref, bool targetlist)
{
    List* fields = cref->fields;
    int numnames = list_length(fields);

    if (numnames == 1) {
        /*
         * 目标项是裸露的'*'，展开所有表
         * （例如，SELECT * FROM emp, dept）
         *
         * 由于语法仅在SELECT的顶层接受裸露的'*'，我们在这里不需要处理targetlist==false的情况。
         */
        AssertEreport(targetlist, MOD_OPT, "");
        return ExpandAllTables(pstate, cref->location);
    } else {
        /*
         * 目标项是 relation.*，展开指定的表
         * （例如，SELECT emp.*, dname FROM emp, dept）
         *
         * 注意：此代码与transformColumnRef很相似；调用该函数然后替换结果的整行Var为Var的列表。但是，
         * 这会导致我们的RTE的selectedCols位图显示整行以及个别列都需要select权限，这是不正确的
         * （因为后来添加的列不应该需要select权限）。我们可以尝试在事后删除整行权限位，但复制代码更整洁。
         */
        char* nspname = NULL;
        char* relname = NULL;
        RangeTblEntry* rte = NULL;
        int levels_up;
        enum { CRSERR_NO_RTE, CRSERR_WRONG_DB, CRSERR_TOO_MANY } crserr = CRSERR_NO_RTE;

        /*
         * 首先给予PreParseColumnRefHook，如果有的话，第一次尝试。如果返回非空，则应使用该表达式。
         */
        if (pstate->p_pre_columnref_hook != NULL) {
            Node* node = NULL;

            node = (*pstate->p_pre_columnref_hook)(pstate, cref);
            if (node != NULL) {
                return ExpandRowReference(pstate, node, targetlist);
            }
        }

        switch (numnames) {
            case 2:
                relname = strVal(linitial(fields));
                rte = refnameRangeTblEntry(pstate, nspname, relname, cref->location, &levels_up);
                break;
            case 3:
                nspname = strVal(linitial(fields));
                relname = strVal(lsecond(fields));
                rte = refnameRangeTblEntry(pstate, nspname, relname, cref->location, &levels_up);
                break;
            case 4: {
                char* catname = strVal(linitial(fields));

                /*
                 * 检查目录名称，然后忽略它。
                 */
                if (strcmp(catname, get_and_check_db_name(u_sess->proc_cxt.MyDatabaseId, false)) != 0) {
                    crserr = CRSERR_WRONG_DB;
                    break;
                }
                nspname = strVal(lsecond(fields));
                relname = strVal(lthird(fields));
                rte = refnameRangeTblEntry(pstate, nspname, relname, cref->location, &levels_up);
                break;
            }
            default:
                crserr = CRSERR_TOO_MANY;
                break;
        }

        /*
         * 现在给PostParseColumnRefHook，如果有的话，一次机会。我们通过传递RangeTblEntry而不是Var，有点作弊。
         * （单个Var也不完全正确。这种约定允许真正关心的钩子知道正在发生什么。）
         */
        if (pstate->p_post_columnref_hook != NULL) {
            Node* node = NULL;

            node = (*pstate->p_post_columnref_hook)(pstate, cref, (Node*)rte);
            if (node != NULL) {
                if (rte != NULL) {
                    ereport(ERROR,
                        (errcode(ERRCODE_AMBIGUOUS_COLUMN),
                            errmsg("column reference \"%s\" is ambiguous", NameListToString(cref->fields)),
                            parser_errposition(pstate, cref->location)));
                }
                return ExpandRowReference(pstate, node, targetlist);
            }
        }

        /*
         * 如果找不到翻译，则抛出错误。
         */
        if (rte == NULL) {
            switch (crserr) {
                case CRSERR_NO_RTE:
                    errorMissingRTE(pstate, makeRangeVar(nspname, relname, cref->location));
                    break;
                case CRSERR_WRONG_DB:
                    ereport(ERROR,
                        (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                            errmsg("cross-database references are not implemented: %s", NameListToString(cref->fields)),
                            parser_errposition(pstate, cref->location)));
                    break;
                case CRSERR_TOO_MANY:
                    ereport(ERROR,
                        (errcode(ERRCODE_SYNTAX_ERROR),
                            errmsg(
                                "improper qualified name (too many dotted names): %s", NameListToString(cref->fields)),
                            parser_errposition(pstate, cref->location)));
                    break;
                default:
                    break;
            }
        }

        /*
         * 好的，展开RTE到字段中。
         */
        return ExpandSingleTable(pstate, rte, cref->location, targetlist);
    }
}

/*
 * ExpandAllTables()
 *		将'*'（在目标列表中）转换为目标列表条目的列表。
 *
 * 为查询的varnamespace中出现的每个关系生成tlist条目。
 * 我们不考虑relnamespace，因为那会包括没有别名JOIN的输入表，NEW/OLD伪条目等。
 *
 * 被引用的关系/列被标记为需要SELECT访问。
 */
static List* ExpandAllTables(ParseState* pstate, int location)
{
    List* target = NIL;
    ListCell* l = NULL;

    /* 检查是否为SELECT *; */
    if (!pstate->p_varnamespace) {
        ereport(ERROR,
            (errcode(ERRCODE_SYNTAX_ERROR),
                errmsg("SELECT * with no tables specified is not valid"),
                parser_errposition(pstate, location)));
    }
    /* 添加星号信息（起始，结束，仅限）*/
    pstate->p_star_start = lappend_int(pstate->p_star_start, pstate->p_next_resno);
    pstate->p_star_only = lappend_int(pstate->p_star_only, 1);
    foreach (l, pstate->p_varnamespace) {
        ParseNamespaceItem *nsitem = (ParseNamespaceItem *)lfirst(l);
        RangeTblEntry *rte = nsitem->p_rte;
        int rtindex = RTERangeTablePosn(pstate, rte, NULL);

        /* 在解析目标列表时不应该有任何仅lateral的项目 */
        Assert(!nsitem->p_lateral_only);

        target = list_concat(target, expandRelAttrs(pstate, rte, rtindex, 0, location));
    }
    pstate->p_star_end = lappend_int(pstate->p_star_end, pstate->p_next_resno);

    return target;
}

/*
 * ExpandIndirectionStar()
 * 将 foo.* 转换为表达式列表或目标列表条目。
 * 处理 '*' 出现在 A_Indirection 的最后一项的情况。
 * 代码在 SELECT 目标列表中使用时生成 TargetEntry 节点，而在 ROW() 或 VALUES() 构造中只生成裸露的表达式。
 */
static List* ExpandIndirectionStar(ParseState* pstate, A_Indirection* ind, bool targetlist, ParseExprKind exprKind)
{
    Node* expr = NULL;

    /* 剥去 '*'，创建对行类型对象的引用 */
    ind = (A_Indirection*)copyObject(ind);
    ind->indirection = list_truncate(ind->indirection, list_length(ind->indirection) - 1);

    /* 然后对其进行转换 */
    expr = transformExpr(pstate, (Node*)ind, exprKind);

    /* 将行类型表达式展开为单个字段 */
    return ExpandRowReference(pstate, expr, targetlist);
}

/*
 * ExpandSingleTable()
 * 将 foo.* 转换为表达式列表或目标列表条目。
 * 处理 foo 被确定为对 RTE 的简单引用的情况，因此我们可以为表达式生成 Vars。
 * 被引用的列会被标记为需要 SELECT 访问。
 */
static List* ExpandSingleTable(ParseState* pstate, RangeTblEntry* rte, int location, bool targetlist)
{
    int sublevels_up;
    int rtindex;

    rtindex = RTERangeTablePosn(pstate, rte, &sublevels_up);

    if (targetlist) {
        List* te_list = NIL;

        /* 类似于 foo.*，标记标志位 */
        pstate->p_star_start = lappend_int(pstate->p_star_start, pstate->p_next_resno);
        pstate->p_star_only = lappend_int(pstate->p_star_only, -1);

        /* expandRelAttrs 处理权限标记 */
        te_list = expandRelAttrs(pstate, rte, rtindex, sublevels_up, location);
        pstate->p_star_end = lappend_int(pstate->p_star_end, pstate->p_next_resno);

        return te_list;
    } else {
        List* vars = NIL;
        ListCell* l = NULL;

        expandRTE(rte, rtindex, sublevels_up, location, false, NULL, &vars);

        /* 需要对表进行读取访问权限 */
        rte->requiredPerms |= ACL_SELECT;

        /* 需要对每一列进行读取访问权限 */
        foreach (l, vars) {
            Var* var = (Var*)lfirst(l);
            markVarForSelectPriv(pstate, var, rte);
        }

        return vars;
    }
}

/*
 * ExpandRowReference()
 * 将 foo.* 转换为表达式列表或目标列表条目。
 * 处理 foo 是任意表达式的复合类型的情况。
 */
static List* ExpandRowReference(ParseState* pstate, Node* expr, bool targetlist)
{
    List* result = NIL;
    TupleDesc tupleDesc;
    int numAttrs;
    int i;

    /*
     * 如果行类型表达式是整行 Var，则我们可以将字段展开为简单的 Var。
     * 注意：如果 RTE 是一个关系，则这种情况会使得 RTE 的 selectedCols 位图显示整行需要选择权限，以及单个列。
     * 但这种情况只有在出现奇怪的记法时才会出现，例如 (table.*).*
     */
    if (IsA(expr, Var) && ((Var*)expr)->varattno == InvalidAttrNumber) {
        Var* var = (Var*)expr;
        RangeTblEntry* rte = NULL;

        rte = GetRTEByRangeTablePosn(pstate, var->varno, var->varlevelsup);
        return ExpandSingleTable(pstate, rte, var->location, targetlist);
    }

    /*
     * 否则，我们得用比较困难的方式。我们当前的实现是生成多份表达式的副本并进行 FieldSelect 操作。
     * 如果表达式涉及到复杂的计算，这种方式可能效率较低。
     *
     * 验证它是否为复合类型，并获取 tupdesc。我们使用 get_expr_result_type()，因为它可以处理对返回匿名记录类型的函数的引用。
     * 如果失败，则使用 lookup_rowtype_tupdesc_copy()，它几乎肯定也会失败，但会提供适当的错误消息。
     *
     * 如果它是 Var 类型且类型为 RECORD，则我们必须更加努力：
     * 我们必须找到 Var 引用的内容，并将其传递给 get_expr_result_type。
     * 这个任务由 expandRecordVariable() 处理。
     */
    if (IsA(expr, Var) && ((Var*)expr)->vartype == RECORDOID) {
        tupleDesc = expandRecordVariable(pstate, (Var*)expr, 0);
    } else if (get_expr_result_type(expr, NULL, &tupleDesc) != TYPEFUNC_COMPOSITE) {
        tupleDesc = lookup_rowtype_tupdesc_copy(exprType(expr), exprTypmod(expr));
    }

    if (unlikely(tupleDesc == NULL)) {
        ereport(ERROR,
            (errcode(ERRCODE_UNEXPECTED_NULL_VALUE),
                errmsg("tupleDesc should not be null")));
    }

    /* 生成对各个字段的引用列表 */
    numAttrs = tupleDesc->natts;
    for (i = 0; i < numAttrs; i++) {
        Form_pg_attribute att = &tupleDesc->attrs[i];
        FieldSelect* fselect = NULL;

        if (att->attisdropped) {
            continue;
        }
        fselect = makeNode(FieldSelect);
        fselect->arg = (Expr*)copyObject(expr);
        fselect->fieldnum = i + 1;
        fselect->resulttype = att->atttypid;
        fselect->resulttypmod = att->atttypmod;
        /* 保存属性的排序规则，供 parse_collate.c 使用 */
        fselect->resultcollid = att->attcollation;

        if (targetlist) {
            /* 添加 TargetEntry 装饰 */
            TargetEntry* te = NULL;

            te = makeTargetEntry(
                (Expr*)fselect, (AttrNumber)pstate->p_next_resno++, pstrdup(NameStr(att->attname)), false);
            result = lappend(result, te);
        } else {
            result = lappend(result, fselect);
        }
    }

    return result;
}

/*
 * expandRecordVariable
 *		如果可能，获取类型为RECORD的Var的元组描述符。
 *
 * 由于实际表或视图列不允许具有类型为RECORD的列，因此这样的Var必须引用JOIN或FUNCTION RTE或子查询输出。
 * 我们深入到底部以查找最终定义表达式，并尝试从中推断出元组描述符。如果我们无法确定元组描述符，就会产生错误。
 *
 * levelsup是一个额外的偏移量，用于正确解释Var的varlevelsup。
 */
TupleDesc expandRecordVariable(ParseState* pstate, Var* var, int levelsup)
{
    TupleDesc tupleDesc;
    int netlevelsup;
    RangeTblEntry* rte = NULL;
    AttrNumber attnum;
    Node* expr = NULL;

    /* 检查调用者没有弄错 */
    AssertEreport(IsA(var, Var), MOD_OPT, "");
    AssertEreport(var->vartype == RECORDOID, MOD_OPT, "");

    netlevelsup = var->varlevelsup + levelsup;
    rte = GetRTEByRangeTablePosn(pstate, var->varno, netlevelsup);
    attnum = var->varattno;

    if (attnum == InvalidAttrNumber) {
        /* 对RTE的整行引用，因此展开已知字段 */
        List* names = NIL;
        List* vars = NIL;
        ListCell* lname = NULL;
        ListCell* lvar = NULL;
        int i;

        expandRTE(rte, var->varno, 0, var->location, false, &names, &vars);

        tupleDesc = CreateTemplateTupleDesc(list_length(vars), false);
        i = 1;
        forboth(lname, names, lvar, vars)
        {
            char* label = strVal(lfirst(lname));
            Node* varnode = (Node*)lfirst(lvar);

            TupleDescInitEntry(tupleDesc, i, label, exprType(varnode), exprTypmod(varnode), 0);
            TupleDescInitEntryCollation(tupleDesc, i, exprCollation(varnode));
            i++;
        }
        AssertEreport(lname == NULL && lvar == NULL, MOD_OPT, ""); /* 列表长度相同吗？ */

        return tupleDesc;
    }

    expr = (Node*)var; /* 如果我们无法深入，使用默认值 */

    switch (rte->rtekind) {
        case RTE_RELATION:
        case RTE_VALUES:
        case RTE_RESULT:
            /*
             * 这种情况不应该发生：表或值列表的列不应该具有类型为RECORD的列。继续并在底部失败（最有可能）。
             */
            break;
        case RTE_SUBQUERY: {
            /* FROM中的子查询：检查子选择的输出表达式 */
            TargetEntry* ste = get_tle_by_resno(rte->subquery->targetList, attnum);

            if (ste == NULL || ste->resjunk) {
                ereport(ERROR,
                    (errcode(ERRCODE_OPTIMIZER_INCONSISTENT_STATE),
                        errmsg("subquery %s does not have attribute %d", rte->eref->aliasname, attnum)));
            }
            expr = (Node*)ste->expr;
            if (IsA(expr, Var)) {
                /*
                 * 递归进入子选择，查看其Var引用的内容。我们必须建立一个额外的ParseState级别，以保持在子选择中的varlevelsup同步。
                 */
                ParseState mypstate;
                errno_t rc;

                rc = memset_s(&mypstate, sizeof(mypstate), 0, sizeof(mypstate));
                securec_check(rc, "\0", "\0");
                mypstate.parentParseState = pstate;
                mypstate.p_rtable = rte->subquery->rtable;
                /* 不要费心填充假pstate的其余部分 */
                return expandRecordVariable(&mypstate, (Var*)expr, 0);
            }
            /* 否则，继续检查表达式 */
        } break;
        case RTE_JOIN:
            /* Join RTE --- 递归检查别名变量 */
            AssertEreport(attnum > 0 && attnum <= list_length(rte->joinaliasvars), MOD_OPT, "");
            expr = (Node*)list_nth(rte->joinaliasvars, attnum - 1);
            if (IsA(expr, Var)) {
                return expandRecordVariable(pstate, (Var*)expr, netlevelsup);
            }
            /* 否则，继续检查表达式 */
            break;
        case RTE_FUNCTION:

            /*
             * 除非函数声明为其结果列之一具有RECORD，否则我们不可能到达这里。
             */
            break;
        case RTE_CTE:
            /* CTE引用：检查子查询的输出表达式 */
            if (!rte->self_reference) {
                CommonTableExpr* cte = GetCTEForRTE(pstate, rte, netlevelsup);
                TargetEntry* ste = NULL;

                ste = get_tle_by_resno(GetCTETargetList(cte), attnum);
                if (ste == NULL || ste->resjunk) {
                    ereport(ERROR,
                        (errcode(ERRCODE_OPTIMIZER_INCONSISTENT_STATE),
                            errmsg("subquery %s does not have attribute %d", rte->eref->aliasname, attnum)));
                }
                expr = (Node*)ste->expr;
                if (IsA(expr, Var)) {
                    /*
                     * 递归进入CTE以查看其Var引用的内容。我们必须建立额外的ParseState级别，以保持与CTE中的varlevelsup同步；此外，它可能是外部CTE。
                     */
                    ParseState mypstate;
                    Index levelsup;
                    errno_t rc = EOK;

                    rc = memset_s(&mypstate, sizeof(mypstate), 0, sizeof(mypstate));
                    securec_check(rc, "\0", "\0");
                    /* 这个循环必须工作，因为GetCTEForRTE做了 */
                    for (levelsup = 0; levelsup < rte->ctelevelsup + netlevelsup; levelsup++) {
                        pstate = pstate->parentParseState;
                    }
                    mypstate.parentParseState = pstate;
                    mypstate.p_rtable = ((Query*)cte->ctequery)->rtable;
                    /* 不要费心填充假pstate的其余部分 */

                    return expandRecordVariable(&mypstate, (Var*)expr, 0);
                }
                /* 否则，继续检查表达式 */
            }
            break;
#ifdef PGXC
        case RTE_REMOTE_DUMMY:
            ereport(ERROR, (errcode(ERRCODE_INVALID_OPERATION), errmsg("Invalid RTE found")));
            break;
#endif /* PGXC */
        default:
            break;
    }

    /*
     * 现在我们有一个我们不能展开的表达式，因此看看get_expr_result_type()是否能够处理它。如果不行，就传递给lookup_rowtype_tupdesc()，它可能会失败，但会提供适当的错误消息。
     */
    if (get_expr_result_type(expr, NULL, &tupleDesc) != TYPEFUNC_COMPOSITE) {
        tupleDesc = lookup_rowtype_tupdesc_copy(exprType(expr), exprTypmod(expr));
    }

    return tupleDesc;
}

/*
 * FigureColname -
 *	  如果在目标列表中未指定结果列的名称，我们必须猜测一个合适的名称。SQL规范提供了一些指导，但不多...
 *
 * 请注意，参数是目标项的*未转换*解析树。这比转换后的树稍微容易处理。
 */
char* FigureColname(Node* node)
{
    char* name = NULL;

    (void)FigureColnameInternal(node, &name);
    if (name != NULL) {
        return name;
    }
    /* 如果我们无法猜出任何东西，返回默认结果 */
    return (char*)"?column?";
}

/*
 * FigureIndexColname -
 *	  为索引中的表达式列选择名称
 *
 * 实际上这与FigureColname几乎相同，只是如果我们无法选择一个好的名称，我们返回NULL。
 */
char* FigureIndexColname(Node* node)
{
    char* name = NULL;

    (void)FigureColnameInternal(node, &name);
    return name;
}


/*
 * FigureColnameInternal -
 *	  FigureColname的内部工作函数
 *
 * 返回值表示对结果的信心程度：
 *		0 - 无信息
 *		1 - 次佳列名选择
 *		2 - 良好列名选择
 * 返回值实际上仅在内部使用。
 * 如果结果不为零，*name将被设置为所选的名称。
 */
static int FigureColnameInternal(Node* node, char** name)
{
    int strength = 0;

    if (node == NULL) {
        return strength;
    }
    switch (nodeTag(node)) {
        case T_ColumnRef: {
            char* fname = find_last_field_name(((ColumnRef*)node)->fields);
            if (fname != NULL) {
                *name = fname;
                return 2;
            }
        } break;
        case T_A_Indirection: {
            A_Indirection* ind = (A_Indirection*)node;
            char* fname = find_last_field_name(ind->indirection);
            if (fname != NULL) {
                *name = fname;
                return 2;
            }
            return FigureColnameInternal(ind->arg, name);
        } break;
        case T_FuncCall:
            if (((FuncCall*)node)->colname != NULL) {
                *name = ((FuncCall*)node)->colname;
            } else {
                *name = strVal(llast(((FuncCall*)node)->funcname));
            }
            return 2;
        case T_A_Expr:
            /* 使nullif()表现得像常规函数一样 */
            if (((A_Expr*)node)->kind == AEXPR_NULLIF) {
                *name = "nullif";
                return 2;
            }
            break;
        case T_PredictByFunction: {
            size_t len = strlen(((PredictByFunction*)node)->model_name) + strlen("_pred") + 1;
            char* colname = (char*)palloc0(len);
            errno_t rc = snprintf_s(colname, len, len - 1, "%s_pred", ((PredictByFunction*)node)->model_name);
            securec_check_ss(rc, "\0", "\0");
            *name = colname;
            return 1;
        } break;    
        case T_TypeCast:
            strength = FigureColnameInternal(((TypeCast*)node)->arg, name);
            if (strength <= 1) {
                if (((TypeCast*)node)->typname != NULL) {
                    *name = strVal(llast(((TypeCast*)node)->typname->names));
                    return 1;
                }
            }
            break;
        case T_CollateClause:
            return FigureColnameInternal(((CollateClause*)node)->arg, name);
        case T_GroupingFunc:
            /* 使GROUPING()表现得像常规函数一样 */
            *name = "grouping";
            return 2;
        case T_Rownum:
            *name = "rownum";
            return 2;
        case T_SubLink:
            switch (((SubLink*)node)->subLinkType) {
                case EXISTS_SUBLINK:
                    *name = "exists";
                    return 2;
                case ARRAY_SUBLINK:
                    *name = "array";
                    return 2;
                case EXPR_SUBLINK: {
                    /* 获取子查询的单个目标的列名 */
                    SubLink* sublink = (SubLink*)node;
                    Query* query = (Query*)sublink->subselect;

                    /*
                     * 子查询可能已经被转换，但我们要小心并检查。
                     * (我们在这里看到一个转换后的子查询的原因是，
                     * transformSubLink是惰性的，会就地修改SubLink节点。)
                     */
                    if (IsA(query, Query)) {
                        TargetEntry* te = (TargetEntry*)linitial(query->targetList);

                        if (te->resname) {
                            *name = te->resname;
                            return 2;
                        }
                    }
                } break;
                    /* 与其他类似运算符的节点一样，这些没有名称 */
                case ALL_SUBLINK:
                case ANY_SUBLINK:
                case ROWCOMPARE_SUBLINK:
                case CTE_SUBLINK:
#ifdef USE_SPQ
                case NOT_EXISTS_SUBLINK:
#endif
                    break;
            }
            break;
        case T_CaseExpr:
            strength = FigureColnameInternal((Node*)((CaseExpr*)node)->defresult, name);
            if (strength <= 1) {
                *name = "case";
                return 1;
            }
            break;
        case T_A_ArrayExpr:
            /* 使ARRAY[]表现得像常规函数一样 */
            *name = "array";
            return 2;
        case T_RowExpr:
            /* 使ROW()表现得像常规函数一样 */
            *name = "row";
            return 2;
        case T_CoalesceExpr:
            /* 使coalesce()表现得像常规函数一样 */
            // 将NVL显示修改为A数据库的样式"NVL"，而不是"COALESCE"
            if (((CoalesceExpr*)node)->isnvl) {
                *name = "nvl";
            } else {
                *name = "coalesce";
            }
            return 2;
        case T_MinMaxExpr:
            /* 使greatest/least表现得像常规函数一样 */
            switch (((MinMaxExpr*)node)->op) {
                case IS_GREATEST:
                    *name = "greatest";
                    return 2;
                case IS_LEAST:
                    *name = "least";
                    return 2;
            }
            break;
        case T_XmlExpr:
            /* 使SQL/XML函数表现得像常规函数一样 */
            switch (((XmlExpr*)node)->op) {
                case IS_XMLCONCAT:
                    *name = "xmlconcat";
                    return 2;
                case IS_XMLELEMENT:
                    *name = "xmlelement";
                    return 2;
                case IS_XMLFOREST:
                    *name = "xmlforest";
                    return 2;
                case IS_XMLPARSE:
                    *name = "xmlparse";
                    return 2;
                case IS_XMLPI:
                    *name = "xmlpi";
                    return 2;
                case IS_XMLROOT:
                    *name = "xmlroot";
                    return 2;
                case IS_XMLSERIALIZE:
                    *name = "xmlserialize";
                    return 2;
                case IS_DOCUMENT:
                    /* 无操作 */
                    break;
            }
            break;
        case T_XmlSerialize:
            *name = "xmlserialize";
            return 2;
        /* 获取用户定义变量的名称。 */
        case T_UserVar: {
            size_t len = strlen(((UserVar *)node)->name) + strlen("@") + 1;
            char *colname = (char *)palloc0(len);
            errno_t rc = snprintf_s(colname, len, len - 1, "@%s", ((UserVar *)node)->name);
            securec_check_ss(rc, "\0", "\0");
            *name = colname;
            return 1;
        } break;
        default:
            break;
    }

    return strength;
}

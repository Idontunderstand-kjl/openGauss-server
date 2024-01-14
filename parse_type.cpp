/* -------------------------------------------------------------------------
 *
 * parse_type.cpp
 *		handle type operations for parser
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 * Portions Copyright (c) 2021, openGauss Contributors
 *
 *
 * IDENTIFICATION
 *	  src/common/backend/parser/parse_type.cpp
 *
 * -------------------------------------------------------------------------
 */
#include "postgres.h"
#include "knl/knl_variable.h"
#include "gaussdb_version.h"

#include "access/transam.h"
#include "catalog/namespace.h"
#include "catalog/gs_package.h"
#include "catalog/pg_type.h"
#include "lib/stringinfo.h"
#include "nodes/makefuncs.h"
#include "optimizer/nodegroups.h"
#include "parser/parser.h"
#include "parser/parse_type.h"
#include "pgxc/groupmgr.h"
#include "pgxc/pgxc.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/date.h"
#include "utils/datum.h"
#include "utils/fmgrtab.h"
#include "utils/lsyscache.h"
#include "utils/timestamp.h"
#include "utils/syscache.h"
#include "utils/pl_package.h"
#include "catalog/gs_collation.h"
#include "parser/parse_utilcmd.h"
#include "catalog/pg_object.h"
#include "catalog/gs_dependencies_fn.h"
#include "catalog/pg_type_fn.h"

/*
 * LookupPctTypeInPackage
 * 在指定的包中查找给定表的类型。
 */
Oid LookupPctTypeInPackage(RangeVar* rel, Oid pkgOid, const char* field)
{
    // 生成类型名并进行类型转换
    char* castTypeName = CastPackageTypeName(rel->relname, pkgOid, true);
    char* oldTypName = rel->relname;
    rel->relname = castTypeName;

    // 获取关系的Oid
    Oid relid = RangeVarGetRelidExtended(rel, NoLock, true, false, false, true, NULL, NULL, NULL, NULL);
    if (!OidIsValid(relid)) {
        // 如果未找到关系，恢复原始表名并释放资源
        rel->relname = oldTypName;
        pfree_ext(castTypeName);
        return InvalidOid;
    }

    // 获取字段在表中的属性号
    AttrNumber attnum = get_attnum(relid, field);
    if (attnum == InvalidAttrNumber) {
        // 如果属性号无效，恢复原始表名并释放资源
        rel->relname = oldTypName;
        pfree_ext(castTypeName);
        return InvalidOid;
    }

    // 获取属性的数据类型
    Oid typoid = get_atttype(relid, attnum);
    rel->relname = oldTypName;
    pfree_ext(castTypeName);

    if (OidIsValid(typoid)) {
        return relid;
    } else {
        return InvalidOid;
    }
}

/*
 * LookupTypeNameSupportUndef
 * 在支持未定义类型的情况下查找类型名。
 */
Type LookupTypeNameSupportUndef(ParseState *pstate, const TypeName *typeName, int32 *typmod_p, bool print_notice)
{
    Type typtup = NULL;
    // 保存旧的CreatePlsqlType函数并设置特殊标志位
    CreatePlsqlType oldCreatePlsqlType = u_sess->plsql_cxt.createPlsqlType;
    PG_TRY();
    {
        set_create_plsql_type_not_check_nsp_oid();
        // 创建类型依赖关系扩展对象
        TypeDependExtend* dependExt = NULL;
        InstanceTypeNameDependExtend(&dependExt);

        // 调用LookupTypeNameExtended函数查找类型名
        typtup = LookupTypeName(pstate, typeName, typmod_p, print_notice, dependExt);
        pfree_ext(dependExt);
    }
    PG_CATCH();
    {
        // 恢复原来的CreatePlsqlType函数并重新抛出异常
        set_create_plsql_type(oldCreatePlsqlType);
        PG_RE_THROW();
    }
    PG_END_TRY();
    // 恢复原来的CreatePlsqlType函数并返回查找结果
    set_create_plsql_type(oldCreatePlsqlType);
    return typtup;
}

/*
 * LookupTypeName
 * 查找类型名的包装器，使用默认参数调用LookupTypeNameExtended函数。
 */
Type LookupTypeName(ParseState *pstate, const TypeName *typeName, int32 *typmod_p, bool print_notice, TypeDependExtend* dependExtend)
{
    return LookupTypeNameExtended(pstate, typeName, typmod_p, true, print_notice, dependExtend);
}


/*
 * LookupTypeNameExtended
 *		Given a TypeName object, lookup the pg_type syscache entry of the type.
 *		Returns NULL if no such type can be found.	If the type is found,
 *		the typmod value represented in the TypeName struct is computed and
 *		stored into *typmod_p.
 *
 * NB: on success, the caller must ReleaseSysCache the type tuple when done
 * with it.
 *
 * NB: direct callers of this function MUST check typisdefined before assuming
 * that the type is fully valid.  Most code should go through typenameType
 * or typenameTypeId instead.
 *
 * typmod_p can be passed as NULL if the caller does not care to know the
 * typmod value, but the typmod decoration (if any) will be validated anyway,
 * except in the case where the type is not found.	Note that if the type is
 * found but is a shell, and there is typmod decoration, an error will be
 * thrown --- this is intentional.
 *
 * If temp_ok is false, ignore types in the temporary namespace.  Pass false
 * when the caller will decide, using goodness of fit criteria, whether the
 * typeName is actually a type or something else.  If typeName always denotes
 * a type (or denotes nothing), pass true.
 *
 * pstate is only used for error location info, and may be NULL.
 */
/*
 * Type LookupTypeNameExtended(ParseState* pstate, const TypeName* typname, int32* typmod_p,
 *                              bool temp_ok, bool print_notice, TypeDependExtend* dependExtend)
 *
 * 在给定的解析状态中查找并返回类型信息。支持 %TYPE 引用，用于引用现有字段的类型。
 *
 * 参数：
 *  - pstate: 解析状态
 *  - typname: 类型名称结构
 *  - typmod_p: 类型修饰符指针
 *  - temp_ok: 是否允许使用临时类型
 *  - print_notice: 是否打印提示信息
 *  - dependExtend: 类型依赖扩展结构
 *
 * 返回值：
 *  - 查找到的类型的 HeapTuple 表示
 */
Type LookupTypeNameExtended(ParseState* pstate, const TypeName* typname, int32* typmod_p,
                            bool temp_ok, bool print_notice, TypeDependExtend* dependExtend)
{
    Oid typoid = InvalidOid;
    HeapTuple tup = NULL;
    int32 typmod = -1;
    Oid pkgOid = InvalidOid;
    bool notPkgType = false;
    char* schemaname = NULL;
    char* typeName = NULL;
    char* pkgName = NULL;

    // 如果类型名称列表为空，说明已经有了类型的 OID
    if (typname->names == NIL) {
        typoid = typname->typeOid;  // 直接使用传入的类型 OID
    } else if (typname->pct_type) {
        // 处理 %TYPE 引用现有字段的类型的情况
        RangeVar* rel = makeRangeVar(NULL, NULL, typname->location);
        char* field = NULL;
        Oid relid = InvalidOid;
        AttrNumber attnum = InvalidAttrNumber;
        char* pkgName = NULL;
        char* schemaName = NULL;

        // 解构名称列表
        int typTupStatus = InvalidTypeTup;
        switch (list_length(typname->names)) {
            case 1:
                // 单一名称，可能是内部生成的 TypeName
                tup = getPLpgsqlVarTypeTup(strVal(linitial(typname->names)));
                typTupStatus = GetTypeTupStatus(tup);
                if (typTupStatus == NormalTypeTup) {
                    return (Type)tup;
                }
                ereport(ERROR,
                    (errcode(ERRCODE_SYNTAX_ERROR),
                        errmsg(
                            "improper %%TYPE reference (too few dotted names): %s", NameListToString(typname->names)),
                        parser_errposition(pstate, typname->location)));
                break;
            case 2:
                // 两个名称，可能是字段的类型引用
                tup = FindPkgVariableType(pstate, typname, typmod_p, dependExtend);
                typTupStatus = GetTypeTupStatus(tup);
                if (typTupStatus == NormalTypeTup) {
                    return (Type)tup;
                }
                rel->relname = strVal(linitial(typname->names));
                field = strVal(lsecond(typname->names));
                break;
            case 3:
                // 三个名称，可能是包内字段的类型引用
                tup = FindPkgVariableType(pstate, typname, typmod_p, dependExtend);
                typTupStatus = GetTypeTupStatus(tup);
                if (typTupStatus == NormalTypeTup) {
                    return (Type)tup;
                }
                pkgName = strVal(linitial(typname->names));
                pkgOid = PackageNameGetOid(pkgName, InvalidOid);
                if (OidIsValid(pkgOid)) {
                    rel->relname = CastPackageTypeName(strVal(lsecond(typname->names)), pkgOid, true);
                } else {
                    rel->schemaname = strVal(linitial(typname->names));
                    rel->relname = strVal(lsecond(typname->names));
                }
                field = strVal(lthird(typname->names));
                break;
            case 4:
                // 四个名称，可能是指定模式的包内字段的类型引用或者是全名引用
                tup = FindPkgVariableType(pstate, typname, typmod_p, dependExtend);
                typTupStatus = GetTypeTupStatus(tup);
                if (typTupStatus == NormalTypeTup) {
                    return (Type)tup;
                }
                pkgName = strVal(lsecond(typname->names));
                schemaName = strVal(linitial(typname->names));
                pkgOid = PackageNameGetOid(pkgName, get_namespace_oid(schemaName, true));
                if (OidIsValid(pkgOid)) {
                    rel->relname = CastPackageTypeName(strVal(lthird(typname->names)), pkgOid, true);
                    rel->schemaname = schemaName;
                } else {
                    rel->catalogname = strVal(linitial(typname->names));
                    rel->schemaname = strVal(lsecond(typname->names));
                    rel->relname = strVal(lthird(typname->names));
                }
                field = strVal(lfourth(typname->names));
                break;
            default:
                ereport(ERROR,
                    (errcode(ERRCODE_SYNTAX_ERROR),
                        errmsg(
                            "improper %%TYPE reference (too many dotted names): %s", NameListToString(typname->names)),
                        parser_errposition(pstate, typname->location)));
                break;
        }

        // 查找字段
        if (u_sess->plsql_cxt.curr_compile_context != NULL &&
            u_sess->plsql_cxt.curr_compile_context->plpgsql_curr_compile_package != NULL) {
            relid = LookupPctTypeInPackage(rel,
                u_sess->plsql_cxt.curr_compile_context->plpgsql_curr_compile_package->pkg_oid, field);
        }
        if (!OidIsValid(relid)) {
            if (enable_plpgsql_undefined()) {
                relid = RangeVarGetRelidExtended(rel, NoLock, true, false, false, true, NULL, NULL, NULL, NULL);
                if (!OidIsValid(relid) && HeapTupleIsValid(tup)) {
                    if (NULL != dependExtend) {
                        dependExtend->dependUndefined = true;
                    }
                    if (GetCurrCompilePgObjStatus() &&
                        u_sess->plsql_cxt.functionStyleType != FUNCTION_STYLE_TYPE_REFRESH_HEAD) {
                        ereport(WARNING,
                            (errcode(ERRCODE_UNDEFINED_OBJECT),
                                errmsg("TYPE %s does not exist in type.", rel->relname)));
                    }
                    InvalidateCurrCompilePgObj();
                    return (Type)tup;
                }
            } else {
                relid = RangeVarGetRelidExtended(rel, NoLock, false, false, false, true, NULL, NULL, NULL, NULL);
            }
        }
        attnum = get_attnum(relid, field);
        if (attnum == InvalidAttrNumber) {
            if (enable_plpgsql_undefined()) {
                if (NULL != dependExtend) {
                    dependExtend->dependUndefined = true;
                }
                return SearchSysCache1(TYPEOID, ObjectIdGetDatum(UNDEFINEDOID));
            } else {
                ereport(ERROR,
                    (errcode(ERRCODE_UNDEFINED_COLUMN),
                        errmsg("column \"%s\" of relation \"%s\" does not exist", field, rel->relname),
                        parser_errposition(pstate, typname->location)));
            }
        }
        typoid = get_atttype(relid, attnum);

        if (IsClientLogicType(typoid)) {
            typoid = get_atttypmod(relid, attnum);
        } else {
            typmod = get_atttypmod(relid, attnum);
        }

        if (enable_plpgsql_undefined() && UndefineTypeTup == typTupStatus && NULL != dependExtend) {
            gsplsql_delete_unrefer_depend_obj_oid(dependExtend->undefDependObjOid, false);
            dependExtend->undefDependObjOid = InvalidOid;
            ReleaseSysCache(tup);
            tup = NULL;
        }
        if (enable_plpgsql_gsdependency() && NULL != dependExtend) {
            dependExtend->typeOid = get_rel_type_id(relid);
        }

        // 如果是数组引用，返回数组类型
        if (typname->arrayBounds != NIL) {
            typoid = get_array_type(typoid);
        }

        // 发出提示信息，表明类型引用已转换
        if (print_notice) {
            ereport(NOTICE,
                (errmsg("type reference %s converted to %s", TypeNameToString(typname), format_type_be(typoid))));
        }
        if (OidIsValid(pkgOid)) {
            pfree_ext(rel->relname);
        }

    } } else {
    /* 普通类型引用 */
    /* 处理 %ROWTYPE 引用现有表的类型。 */
    if (typname->pct_rowtype) {
        RangeVar* relvar = NULL;
        /* 解构名称列表 */
        switch (list_length(typname->names)) {
            case 1:
                relvar = makeRangeVar(NULL, strVal(linitial(typname->names)), -1);
                break;
            case 2:
                relvar = makeRangeVar(strVal(linitial(typname->names)), strVal(lsecond(typname->names)), -1);
                break;
            case 3:
                relvar = makeRangeVar(strVal(lsecond(typname->names)), strVal(lthird(typname->names)), -1);
                relvar->catalogname = strVal(linitial(typname->names));
                break;
            default:
                ereport(ERROR,
                    (errcode(ERRCODE_SYNTAX_ERROR),
                        errmsg("improper %%ROWTYPE reference"),
                        errdetail("improper %%ROWTYPE reference (too many dotted names): %s",
                            NameListToString(typname->names)),
                        errcause("syntax error"),
                        erraction("check the relation name for %%ROWTYPE")));
                break;
        }
        Oid class_oid = RangeVarGetRelidExtended(relvar, NoLock, true, false, false, true, NULL, NULL);
        if (!OidIsValid(class_oid)) {
            /* 若为：cursor%rowtype */
            tup = getCursorTypeTup(strVal(linitial(typname->names)));
            if (HeapTupleIsValid(tup)) {
                return (Type)tup;
            }
            if (enable_plpgsql_undefined() && NULL != dependExtend) {
                Oid undefRefObjOid = gsplsql_try_build_exist_schema_undef_table(relvar);
                if (OidIsValid(undefRefObjOid)) {
                    dependExtend->undefDependObjOid = undefRefObjOid;
                    dependExtend->dependUndefined = true;
                    InvalidateCurrCompilePgObj();
                    tup = SearchSysCache1(TYPEOID, ObjectIdGetDatum(UNDEFINEDOID));
                    if (typmod_p != NULL) {
                        *typmod_p = -1;
                    }
                }
            }
            pfree_ext(relvar);
            ereport(NULL != tup ? WARNING : ERROR,
                (errmodule(MOD_PARSER),
                    errcode(ERRCODE_UNDEFINED_TABLE),
                    errmsg("relation does not exist when parse word."),
                    errdetail(" relation \"%s\" referenced by %%ROWTYPE does not exist.",
                            NameListToString(typname->names)),
                    errcause("incorrectly referencing relation"),
                    erraction("check the relation name for %%ROWTYPE")));
            return (Type)tup;
        }
        char relkind = get_rel_relkind(class_oid);
        /* 只允许 %ROWTYPE 引用表 */
        if ((relkind != 'r') && (relkind != 'm')) {
            pfree_ext(relvar);
            ereport(ERROR,
                (errmodule(MOD_PARSER),
                    errcode(ERRCODE_UNDEFINED_TABLE),
                    errmsg("relation does not exist when parse word."),
                    errdetail(" relation \"%s\" referenced by %%ROWTYPE does not exist.",
                            NameListToString(typname->names)),
                    errcause("incorrectly referencing relation"),
                    erraction("check the relation name for %%ROWTYPE")));

        }
        pfree_ext(relvar);
    }

    /* 解构名称列表 */
    DeconstructQualifiedName(typname->names, &schemaname, &typeName, &pkgName);
    Oid namespaceId = InvalidOid;
    if (schemaname != NULL) {
        namespaceId = LookupExplicitNamespace(schemaname);
    }
    bool isPkgType = (pkgName != NULL) &&
        !(list_length(typname->names) == 2 && schemaname != NULL && strcmp(pkgName, typeName) == 0);
    if (isPkgType) {
        /* 类型由包定义，获取转换类型名称 */
        pkgOid = PackageNameGetOid(pkgName, namespaceId);
    }
    if (schemaname != NULL) {
        /* 在包类型中查找 */
        if (isPkgType) {
            typoid = LookupTypeInPackage(typname->names, typeName, pkgOid, namespaceId);
        } else {
            /* 仅在指定模式中查找 */
            typoid = GetSysCacheOid2(TYPENAMENSP, PointerGetDatum(typeName), ObjectIdGetDatum(namespaceId));
        }
        if (!OidIsValid(typoid)) {
            typoid = TryLookForSynonymType(typeName, namespaceId);
            notPkgType = true; /* 需要在重构时修复，还需跟踪类型依赖关系 */
        }
    } else {
        if (pkgName == NULL) {
            /* 首先在当前包中查找类型 */
            typoid = LookupTypeInPackage(typname->names, typeName);
        }
        if (enable_plpgsql_gsdependency_guc()) {
            if (isPkgType) {
                typoid = LookupTypeInPackage(typname->names, typeName, pkgOid);
            } else if (!OidIsValid(typoid)) {
                /* 未限定类型名称，因此搜索搜索路径 */
                typoid = TypenameGetTypidExtended(typeName, temp_ok);
                notPkgType = true; /* 需要在重构时修复，还需跟踪类型依赖关系 */
            }
        } else {
            if (isPkgType) {
                typoid = LookupTypeInPackage(typname->names, typeName, pkgOid);
            }
            if (!OidIsValid(typoid)) {
                /* 未限定类型名称，因此搜索搜索路径 */
                typoid = TypenameGetTypidExtended(typeName, temp_ok);
                notPkgType = true; /* 需要在重构时修复，还需跟踪类型依赖关系 */
            }
        }
    }

    /* 如果是数组引用，返回数组类型 */
    if (typname->arrayBounds != NIL) {
        typoid = get_array_type(typoid);
    }


    /* 处理包依赖关系 */
    if (u_sess->plsql_cxt.need_pkg_dependencies && OidIsValid(pkgOid) && !notPkgType) {
        MemoryContext temp = MemoryContextSwitchTo(SESS_GET_MEM_CXT_GROUP(MEMORY_CONTEXT_OPTIMIZER));
        u_sess->plsql_cxt.pkg_dependencies =
            list_append_unique_oid(u_sess->plsql_cxt.pkg_dependencies, pkgOid);
        MemoryContextSwitchTo(temp);
    }

    if (!OidIsValid(typoid)) {
        if (typmod_p != NULL) {
            *typmod_p = -1;
        }
        if (enable_plpgsql_undefined() && NULL != dependExtend) {
            if (NULL != schemaname && NULL == pkgName && !OidIsValid(get_namespace_oid(schemaname, true))) {
                pkgName = schemaname;
                schemaname = NULL;
            }
            GsDependObjDesc objDesc;
            objDesc.schemaName = schemaname;
            char* activeSchemaName = NULL;
            if (schemaname == NULL) {
                activeSchemaName = get_namespace_name(get_compiled_object_nspoid());
                objDesc.schemaName = activeSchemaName;
            }
            objDesc.packageName = pkgName;
            objDesc.name = typeName;
            objDesc.type = GSDEPEND_OBJECT_TYPE_TYPE;
            if (u_sess->plsql_cxt.functionStyleType != FUNCTION_STYLE_TYPE_REFRESH_HEAD) {
                dependExtend->undefDependObjOid = gsplsql_flush_undef_ref_depend_obj(&objDesc);
            } else {
                dependExtend->undefDependObjOid = InvalidOid;
            }
            dependExtend->dependUndefined = true;
            pfree_ext(activeSchemaName);
            if (GetCurrCompilePgObjStatus() &&
                u_sess->plsql_cxt.functionStyleType != FUNCTION_STYLE_TYPE_REFRESH_HEAD) {
                    ereport(WARNING,
                    (errcode(ERRCODE_UNDEFINED_OBJECT),
                    errmsg("Type %s does not exist.", typeName)));
            }
            InvalidateCurrCompilePgObj();
            tup = SearchSysCache1(TYPEOID, ObjectIdGetDatum(UNDEFINEDOID));
        }
    } else {
        /* 不支持黑名单中的类型。 */
        bool is_unsupported_type = !u_sess->attr.attr_common.IsInplaceUpgrade && IsTypeInBlacklist(typoid);
        if (is_unsupported_type) {
            ereport(ERROR,
                (errcode(ERRCODE_FEATURE_NOT_SUPPORTED), errmsg("type %s is not yet supported.", format_type_be(typoid))));
        }

        tup = SearchSysCache1(TYPEOID, ObjectIdGetDatum(typoid));

        /* 不应发生 */
        if (!HeapTupleIsValid(tup)) {
            ereport(ERROR, (errcode(ERRCODE_CACHE_LOOKUP_FAILED), errmsg("cache lookup failed for type %u", typoid)));
        }
        if (!typname->pct_type) {
            typmod = typenameTypeMod(pstate, typname, (Type)tup);
        }
        if (typmod_p != NULL) {
            *typmod_p = typmod;
        }
    }
    return (Type)tup;
}
/*
 * typenameType - 根据 TypeName 返回 Type 结构和 typmod
 *
 * 与 LookupTypeName 类似，不同之处在于，如果找不到类型或未定义，则会报告适当的错误消息。
 * 因此，调用者可以假定结果是一个完全有效的类型。
 */
Type typenameType(ParseState* pstate, const TypeName* typname, int32* typmod_p, TypeDependExtend* dependExtend)
{
    Type tup;

    tup = LookupTypeName(pstate, typname, typmod_p, true, dependExtend);

    /*
     * 如果类型是关系型的，我们检查表是否在安装组中
     */
    if (!in_logic_cluster() && !IsTypeTableInInstallationGroup(tup)) {
        InsertErrorMessage("type must be in installation group", u_sess->plsql_cxt.plpgsql_yylloc);
        ereport(ERROR,
            (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                errmsg("type '%s' must be in installation group", TypeNameToString(typname))));
    }

    if (tup == NULL) {
        InsertErrorMessage("type does not exist", u_sess->plsql_cxt.plpgsql_yylloc);
        ereport(ERROR,
            (errcode(ERRCODE_UNDEFINED_OBJECT),
                errmsg("type \"%s\" does not exist", TypeNameToString(typname)),
                parser_errposition(pstate, typname->location)));
    }
        
    if (!((Form_pg_type)GETSTRUCT(tup))->typisdefined) {
        InsertErrorMessage("type is only a shell", u_sess->plsql_cxt.plpgsql_yylloc);
        ereport(ERROR,
            (errcode(ERRCODE_UNDEFINED_OBJECT),
                errmsg("type \"%s\" is only a shell", TypeNameToString(typname)),
                parser_errposition(pstate, typname->location)));
    }
    return tup;
}

/*
 * typenameTypeId - 根据 TypeName 返回类型的 OID
 *
 * 与 typenameType 类似，但我们只返回类型 OID，而不是 syscache 条目。
 */
Oid typenameTypeId(ParseState* pstate, const TypeName* typname)
{
    Oid typoid;
    Type tup;

    tup = typenameType(pstate, typname, NULL);
    typoid = HeapTupleGetOid(tup);
    ReleaseSysCache(tup);

    return typoid;
}

/*
 * typenameTypeIdAndMod - 根据 TypeName 返回类型的 OID 和 typmod
 *
 * 与 typenameType 类似，但我们只返回类型 OID 和 typmod，而不是 syscache 条目。
 */
void typenameTypeIdAndMod(ParseState* pstate, const TypeName* typname, Oid* typeid_p, int32* typmod_p, TypeDependExtend* dependExtend)
{
    Type tup;

    tup = typenameType(pstate, typname, typmod_p, dependExtend);
    *typeid_p = HeapTupleGetOid(tup);
    ReleaseSysCache(tup);
}

/*
 * typenameTypeMod - 根据 TypeName 返回内部 typmod 值
 *
 * 如果 TypeName 包含数据类型不允许的类型修饰符，将抛出错误。
 *
 * TypeName 表示的实际类型 OID 必须已经被查找，作为 "typ" 参数传递。
 *
 * pstate 仅用于错误位置信息，可能为 NULL。
 */
static int32 typenameTypeMod(ParseState* pstate, const TypeName* typname, Type typ)
{
    int32 result;
    Oid typmodin;
    Datum* datums = NULL;
    int n;
    ListCell* l = NULL;
    ArrayType* arrtypmod = NULL;
    ParseCallbackState pcbstate;

    /* 如果没有类型修饰符表达式，则返回预定的 typmod */
    if (typname->typmods == NIL) {
        return typname->typemod;
    }

    /*
     * 否则，类型最好接受 typmods。对于 shell 类型的情况，我们使用特殊的错误消息，
     * 因为 shell 类型不可能有 typmodin 函数。
     */
    if (!((Form_pg_type)GETSTRUCT(typ))->typisdefined) {
        ereport(ERROR,
            (errcode(ERRCODE_SYNTAX_ERROR),
                errmsg("type modifier cannot be specified for shell type \"%s\"", TypeNameToString(typname)),
                parser_errposition(pstate, typname->location)));
    }

    typmodin = ((Form_pg_type)GETSTRUCT(typ))->typmodin;

    if (typmodin == InvalidOid) {
        ereport(ERROR,
            (errcode(ERRCODE_SYNTAX_ERROR),
                errmsg("type modifier is not allowed for type \"%s\"", TypeNameToString(typname)),
                parser_errposition(pstate, typname->location)));
    }

    /*
     * 将原始语法输出表达式列表转换为 cstring 数组。
     * 目前，我们允许简单的数值常量、字符串字面值和标识符；可能这个列表可以扩展。
     */
    datums = (Datum*)palloc(list_length(typname->typmods) * sizeof(Datum));
    n = 0;
    foreach (l, typname->typmods) {
        Node* tm = (Node*)lfirst(l);
        char* cstr = NULL;

        if (IsA(tm, A_Const)) {
            A_Const* ac = (A_Const*)tm;

            if (IsA(&ac->val, Integer)) {
                const int len = 32;
                cstr = (char*)palloc0(len);
                errno_t rc = snprintf_s(cstr, len, len - 1, "%ld", (long)ac->val.val.ival);
                securec_check_ss(rc, "", "");
            } else if (IsA(&ac->val, Float) || IsA(&ac->val, String)) {
                /* 我们可以直接使用 str 字段。 */
                cstr = ac->val.val.str;
            }
        } else if (IsA(tm, ColumnRef)) {
            ColumnRef* cr = (ColumnRef*)tm;

            if (list_length(cr->fields) == 1 && IsA(linitial(cr->fields), String)) {
                cstr = strVal(linitial(cr->fields));
            }
        }
        if (cstr == NULL) {
            ereport(ERROR,
                (errcode(ERRCODE_SYNTAX_ERROR),
                    errmsg("type modifiers must be simple constants or identifiers"),
                    parser_errposition(pstate, typname->location)));
        }
        datums[n++] = CStringGetDatum(cstr);
    }

    /* 如果类型的 typmodin 函数失败，则安排报告位置 */
    setup_parser_errposition_callback(&pcbstate, pstate, typname->location);

    result = DatumGetInt32(OidFunctionCall1(typmodin, PointerGetDatum(arrtypmod)));

    cancel_parser_errposition_callback(&pcbstate);

    pfree_ext(datums);
    pfree_ext(arrtypmod);

    return result;
}

/*
 * appendTypeNameToBuffer
 *		将 TypeName 的名称附加到 StringInfo 中。这是 TypeNameToString 和 TypeNameListToString 的共享核心。
 *
 * 注意：这必须适用于不描述任何实际类型的 TypeName；它主要用于报告查找错误。
 */
static void appendTypeNameToBuffer(const TypeName* typname, StringInfo string)
{
    if (typname->names != NIL) {
        /* 以原样发射可能有资格的名称 */
        ListCell* l = NULL;

        foreach (l, typname->names) {
            if (l != list_head(typname->names)) {
                appendStringInfoChar(string, '.');
            }
            appendStringInfoString(string, strVal(lfirst(l)));
        }
    } else {
        /* 查找内部指定的类型 */
        appendStringInfoString(string, format_type_be(typname->typeOid));
    }

    /*
     * 根据需要添加装饰，但仅适用于由 LookupTypeName 考虑的字段
     */
    if (typname->pct_type) {
        appendStringInfoString(string, "%TYPE");
    }

    if (typname->arrayBounds != NIL) {
        appendStringInfoString(string, "[]");
    }
}

/*
 * TypeNameToString
 *		生成表示 TypeName 的名称的字符串。
 *
 * 注意：这必须适用于不描述任何实际类型的 TypeName；它主要用于报告查找错误。
 */
char* TypeNameToString(const TypeName* typname)
{
    StringInfoData string;

    initStringInfo(&string);
    appendTypeNameToBuffer(typname, &string);
    return string.data;
}

/*
 * TypeNameListToString
 *		生成表示 TypeName 列表的名称的字符串。
 */
char* TypeNameListToString(List* typenames)
{
    StringInfoData string;
    ListCell* l = NULL;

    initStringInfo(&string);
    foreach (l, typenames) {
        TypeName* typname = (TypeName*)lfirst(l);

        AssertEreport(IsA(typname, TypeName), MOD_OPT, "");
        if (l != list_head(typenames)) {
            appendStringInfoChar(&string, ',');
        }
        appendTypeNameToBuffer(typname, &string);
    }
    return string.data;
}

/*
 * LookupCollation
 *
 * 通过名称查找排序规则，返回 OID，支持错误位置。
 */
Oid LookupCollation(ParseState* pstate, List* collnames, int location)
{
    Oid colloid;
    ParseCallbackState pcbstate;

    if (pstate != NULL) {
        setup_parser_errposition_callback(&pcbstate, pstate, location);
    }

    colloid = get_collation_oid(collnames, false);

    if (pstate != NULL) {
        cancel_parser_errposition_callback(&pcbstate);
    }

    return colloid;
}

Oid get_column_def_collation_b_format(ColumnDef* coldef, Oid typeOid, Oid typcollation,
    bool is_bin_type, Oid rel_coll_oid)
{
    if (coldef->typname->charset != PG_INVALID_ENCODING && !IsSupportCharsetType(typeOid) && !type_is_enum(typeOid) && !type_is_set(typeOid)) {
        ereport(ERROR, (errcode(ERRCODE_DATATYPE_MISMATCH),
                errmsg("type %s not support set charset", format_type_be(typeOid))));
    }

    Oid result = InvalidOid;
    if (!OidIsValid(typcollation) && !is_bin_type && !type_is_set(typeOid)) {
        return InvalidOid;
    } else if (OidIsValid(coldef->collOid)) {
        /* 预先准备好的排序规则规范，使用它 */
        return coldef->collOid;
    }

    char* schemaname = NULL;
    char* collate = NULL;
    if (coldef->collClause) {
        DeconstructQualifiedName(coldef->collClause->collname, &schemaname, &collate);
        if (schemaname != NULL && strcmp(schemaname, "pg_catalog") != 0) {
            ereport(ERROR, (errcode(ERRCODE_UNDEFINED_SCHEMA),
                    errmsg("error schema name for collate")));
        }
    }
    /* 对于二进制类型，如果表的默认排序规则不是 "binary"，则不会继承 rel_coll_oid。*/
    if (is_bin_type) {
        rel_coll_oid = InvalidOid;
    }
    result = transform_default_collation(collate, coldef->typname->charset, rel_coll_oid, true);
    if (!OidIsValid(result)) {
        if (!USE_DEFAULT_COLLATION) {
            result = typcollation;
        } else if (is_bin_type) {
            result = BINARY_COLLATION_OID;
        } else {
            result = get_default_collation_by_charset(GetDatabaseEncoding());
        }
    }
    return result;
}

/*
 * GetColumnDefCollation
 *
 * 获取正在定义的列使用的排序规则，给定 ColumnDef 节点和先前确定的列类型 OID。
 *
 * pstate 仅用于错误位置目的，可以为 NULL。
 */
Oid GetColumnDefCollation(ParseState* pstate, ColumnDef* coldef, Oid typeOid, Oid rel_coll_oid)
{
    Oid result;
    Oid typcollation = get_typcollation(typeOid);
    int location = -1;
    bool is_bin_type = IsBinaryType(typeOid);

    if (DB_IS_CMPT(B_FORMAT)) {
        result = get_column_def_collation_b_format(coldef, typeOid, typcollation, is_bin_type, rel_coll_oid);
    } else if (coldef->collClause) {
        /* 有原始 COLLATE 子句，因此查找排序规则 */
        location = coldef->collClause->location;
        result = LookupCollation(pstate, coldef->collClause->collname, location);
    } else if (OidIsValid(coldef->collOid)) {
        /* 预先准备好的排序规则规范，使用它 */
        result = coldef->collOid;
    } else {
        /* 如果有的话，使用类型的默认排序规则 */
        result = typcollation;
    }

    if (coldef->collClause) {
        check_binary_collation(result, typeOid);
    }
    /* 如果排序规则有效，并且类型没有排序规则，则发出投诉 */
    if (OidIsValid(result) && !OidIsValid(typcollation) && !is_bin_type && !type_is_set(typeOid)) {
        ereport(ERROR,
            (errcode(ERRCODE_DATATYPE_MISMATCH),
                errmsg("collations are not supported by type %s", format_type_be(typeOid)),
                parser_errposition(pstate, location)));
    }

    return result;
}

/* 返回 Type 结构，给定类型 id */
/* 注意：调用方必须在完成后使用 ReleaseSysCache 释放类型元组 */
Type typeidType(Oid id)
{
    HeapTuple tup;

    tup = SearchSysCache1(TYPEOID, ObjectIdGetDatum(id));
    if (!HeapTupleIsValid(tup)) {
        ereport(ERROR, (errcode(ERRCODE_CACHE_LOOKUP_FAILED), errmsg("cache lookup failed for type %u", id)));
    }
    return (Type)tup;
}

/* 
 * 根据类型结构体（Type 结构）返回类型的 OID。
 */
Oid typeTypeId(Type tp)
{
    if (tp == NULL) {
        ereport(ERROR, (errcode(ERRCODE_UNRECOGNIZED_NODE_TYPE), errmsg("typeTypeId() called with NULL type struct")));
    }
    return HeapTupleGetOid(tp);
}

/* 
 * 根据类型结构体（Type 结构）返回类型的长度。
 */
int16 typeLen(Type t)
{
    Form_pg_type typ;

    typ = (Form_pg_type)GETSTRUCT(t);
    return typ->typlen;
}

/* 
 * 根据类型结构体（Type 结构）返回类型是否为按值传递（byval）。
 */
bool typeByVal(Type t)
{
    Form_pg_type typ;

    typ = (Form_pg_type)GETSTRUCT(t);
    return typ->typbyval;
}

/* 
 * 根据类型结构体（Type 结构）返回类型的名称。
 * 注意：使用 pstrdup 复制字符串，因为结果可能需要在系统缓存条目之外保留。
 */
char* typeTypeName(Type t)
{
    Form_pg_type typ;

    typ = (Form_pg_type)GETSTRUCT(t);
    return pstrdup(NameStr(typ->typname));
}

/* 
 * 根据类型结构体（Type 结构）返回类型的 'typrelid' 属性。
 */
Oid typeTypeRelid(Type typ)
{
    Form_pg_type typtup;

    typtup = (Form_pg_type)GETSTRUCT(typ);
    return typtup->typrelid;
}

/* 
 * 根据类型结构体（Type 结构）返回类型的 'typcollation' 属性。
 */
Oid typeTypeCollation(Type typ)
{
    Form_pg_type typtup;

    typtup = (Form_pg_type)GETSTRUCT(typ);
    return typtup->typcollation;
}

/*
 * 给定类型结构体和字符串，返回该字符串的内部表示形式。
 * "string" 参数可以为 NULL 以执行 NULL 的转换（如果输入函数拒绝 NULL，则可能失败）。
 * 当 can_ignore 为 true 时，如果字符串对于目标类型无效，可能会截断或转换。
 */
Datum stringTypeDatum(Type tp, char* string, int32 atttypmod, bool can_ignore)
{
    Form_pg_type typform = (Form_pg_type)GETSTRUCT(tp);
    Oid typinput = typform->typinput;
    Oid typioparam = getTypeIOParam(tp);
    Datum result;

    switch (typinput) {
        case F_DATE_IN:
            result = input_date_in(string, can_ignore);
            break;
        case F_BPCHARIN:
            result = input_bpcharin(string, typioparam, atttypmod);
            break;
        case F_VARCHARIN:
            result = input_varcharin(string, typioparam, atttypmod);
            break;
        case F_TIMESTAMP_IN:
            result = input_timestamp_in(string, typioparam, atttypmod, can_ignore);
            break;
        default:
            result = OidInputFunctionCall(typinput, string, typioparam, atttypmod, can_ignore);
    }

#ifdef RANDOMIZE_ALLOCATED_MEMORY
    /*
     * 对于按引用传递的数据类型，重复转换以查看输入函数是否在结果中留下了任何未初始化的字节。
     * 我们只能在 RANDOMIZE_ALLOCATED_MEMORY 启用时可靠地检测到这一点，因此在没有测试的情况下不予考虑。
     * 我们不希望输入函数中有任何不稳定性的原因是 Const 节点的比较依赖于 datum 的字节比较，
     * 因此如果输入函数留下垃圾，则可能不会将应该相同的子表达式识别为相同。
     * 有关 2008-04-04 的 pgsql-hackers 讨论，请参见。
     */
    if (string && !typform->typbyval) {
        Datum result2;

        result2 = OidInputFunctionCall(typinput, string, typioparam, atttypmod);
        if (!datumIsEqual(result, result2, typform->typbyval, typform->typlen)) {
            elog(WARNING, "type %s has unstable input conversion for \"%s\"", NameStr(typform->typname), string);
        }
    }
#endif

    return result;
}

/*
 * 根据类型ID返回类型的 'typrelid'（关联的关系，如果有）
 */
Oid typeidTypeRelid(Oid type_id)
{
    HeapTuple typeTuple;
    Form_pg_type type;
    Oid result;

    typeTuple = SearchSysCache1(TYPEOID, ObjectIdGetDatum(type_id));
    if (!HeapTupleIsValid(typeTuple))
        ereport(ERROR, (errcode(ERRCODE_CACHE_LOOKUP_FAILED), errmsg("cache lookup failed for type %u", type_id)));

    type = (Form_pg_type)GETSTRUCT(typeTuple);
    result = type->typrelid;
    ReleaseSysCache(typeTuple);
    return result;
}

/*
 * parseTypeString() 的错误回调函数，用于解析失败时进行错误上下文回调
 */
static void pts_error_callback(void* arg)
{
    const char* str = (const char*)arg;

    errcontext("invalid type name \"%s\"", str);

    /*
     * 目前我们只是抑制了语法错误位置报告，而不是转换为“内部查询”错误。
     * 这是因为类型名称不太可能复杂到需要定位。
     */
    errposition(0);
}

/*
 * 给定一个假定为 SQL 兼容类型声明的字符串，例如 "int4" 或 "integer" 或 "character varying(32)"，
 * 解析字符串并将其转换为类型OID和类型修饰符。
 */
void parseTypeString(const char* str, Oid* typeid_p, int32* typmod_p, TypeDependExtend* dependExtend)
{
    StringInfoData buf;
    buf.data = NULL;
    List* raw_parsetree_list = NIL;
    SelectStmt* stmt = NULL;
    ResTarget* restarget = NULL;
    TypeCast* typecast = NULL;
    TypeName* typname = NULL;
    ErrorContextCallback ptserrcontext;

    /* 确保对空输入提供有用的错误信息 */
    if (strspn(str, " \t\n\r\f") == strlen(str)) {
        goto fail;
    }

    initStringInfo(&buf);
    appendStringInfo(&buf, "SELECT NULL::%s", str);

    /*
     * 设置错误回溯支持，以防在解析期间出现 ereport()
     */
    ptserrcontext.callback = pts_error_callback;
    ptserrcontext.arg = (void*)str;
    ptserrcontext.previous = t_thrd.log_cxt.error_context_stack;
    t_thrd.log_cxt.error_context_stack = &ptserrcontext;

    raw_parsetree_list = raw_parser(buf.data);

    t_thrd.log_cxt.error_context_stack = ptserrcontext.previous;

    /*
     * 确保我们得到了精确的预期结果，没有多余的；由于字符串可能包含任何内容，偏执是正当的。
     */
    if (list_length(raw_parsetree_list) != 1)
        goto fail;
    stmt = (SelectStmt*)linitial(raw_parsetree_list);
    if (stmt == NULL || !IsA(stmt, SelectStmt) || stmt->distinctClause != NIL || stmt->intoClause != NULL ||
        stmt->fromClause != NIL || stmt->whereClause != NULL || stmt->groupClause != NIL ||
        stmt->havingClause != NULL || stmt->windowClause != NIL || stmt->withClause != NULL ||
        stmt->valuesLists != NIL || stmt->sortClause != NIL || stmt->limitOffset != NULL || stmt->limitCount != NULL ||
        stmt->lockingClause != NIL || stmt->op != SETOP_NONE) {
        goto fail;
    }
    if (list_length(stmt->targetList) != 1) {
        goto fail;
    }
    restarget = (ResTarget*)linitial(stmt->targetList);
    if (restarget == NULL || !IsA(restarget, ResTarget) || restarget->name != NULL || restarget->indirection != NIL) {
        goto fail;
    }
    typecast = (TypeCast*)restarget->val;
    if (typecast == NULL || !IsA(typecast, TypeCast) || typecast->arg == NULL || !IsA(typecast->arg, A_Const)) {
        goto fail;
    }
    typname = typecast->typname;
    if (typname == NULL || !IsA(typname, TypeName)) {
        goto fail;
    }
    if (typname->setof) {
        goto fail;
    }

    typenameTypeIdAndMod(NULL, typname, typeid_p, typmod_p, dependExtend);

    pfree_ext(buf.data);

    return;

fail:
    pfree_ext(buf.data);
    InsertErrorMessage("invalid type name", u_sess->plsql_cxt.plpgsql_yylloc);
    if (enable_plpgsql_undefined()) {
        InvalidateCurrCompilePgObj();
        *typeid_p = UNDEFINEDOID;
        ereport(WARNING, (errcode(ERRCODE_SYNTAX_ERROR), errmsg("invalid type name \"%s\"", str)));
    } else {
        ereport(ERROR, (errcode(ERRCODE_SYNTAX_ERROR), errmsg("invalid type name \"%s\"", str)));
    }
}

/*
 * 给定一个假定为 SQL 兼容类型声明的字符串，例如 "int4" 或 "integer" 或 "character varying(32)"，
 * 解析字符串并将其作为 TypeName 返回。
 * 如果字符串无法解析为类型，则会引发错误。
 */
TypeName* typeStringToTypeName(const char* str)
{
    StringInfoData buf;
    buf.data = NULL;
    List* raw_parsetree_list = NIL;
    SelectStmt* stmt = NULL;
    ResTarget* restarget = NULL;
    TypeCast* typecast = NULL;
    TypeName* typname = NULL;
    ErrorContextCallback ptserrcontext;

    /* 确保对空输入提供有用的错误信息 */
    if (strspn(str, " \t\n\r\f") == strlen(str)) {
        goto fail;
    }

    initStringInfo(&buf);
    appendStringInfo(&buf, "SELECT NULL::%s", str);

    /*
     * 设置错误回溯支持，以防在解析期间出现 ereport()
     */
    ptserrcontext.callback = pts_error_callback;
    ptserrcontext.arg = (void*)str;
    ptserrcontext.previous = t_thrd.log_cxt.error_context_stack;
    t_thrd.log_cxt.error_context_stack = &ptserrcontext;

    raw_parsetree_list = raw_parser(buf.data);

    t_thrd.log_cxt.error_context_stack = ptserrcontext.previous;

    /*
     * 确保我们得到了精确的预期结果，没有多余的；由于字符串可能包含任何内容，偏执是正当的。
     */
    if (list_length(raw_parsetree_list) != 1)
        goto fail;
    stmt = (SelectStmt*)linitial(raw_parsetree_list);
    if (stmt == NULL || !IsA(stmt, SelectStmt) || stmt->distinctClause != NIL || stmt->intoClause != NULL ||
        stmt->fromClause != NIL || stmt->whereClause != NULL || stmt->groupClause != NIL ||
        stmt->havingClause != NULL || stmt->windowClause != NIL || stmt->withClause != NULL ||
        stmt->valuesLists != NIL || stmt->sortClause != NIL || stmt->limitOffset != NULL || stmt->limitCount != NULL ||
        stmt->lockingClause != NIL || stmt->op != SETOP_NONE) {
        goto fail;
    }
    if (list_length(stmt->targetList) != 1) {
        goto fail;
    }
    restarget = (ResTarget*)linitial(stmt->targetList);
    if (restarget == NULL || !IsA(restarget, ResTarget) || restarget->name != NULL || restarget->indirection != NIL) {
        goto fail;
    }
    typecast = (TypeCast*)restarget->val;
    if (typecast == NULL || !IsA(typecast, TypeCast) || typecast->arg == NULL || !IsA(typecast->arg, A_Const)) {
        goto fail;
    }
    typname = typecast->typname;
    if (typname == NULL || !IsA(typname, TypeName)) {
        goto fail;
    }
    if (typname->setof) {
        goto fail;
    }
    pfree_ext(buf.data);

    return typname;

fail:
    pfree_ext(buf.data);
    ereport(ERROR,
            (errcode(ERRCODE_SYNTAX_ERROR),
             errmsg("invalid type name \"%s\"", str)));
    return NULL;
}

/*
 * IsTypeSupportedByCStore
 *      如果类型受列存储支持，返回true
 *
 * 此函数的性能依赖于编译器对分支进行展开。但是如果编译器无法完成其工作，这也没关系，因为这不是关键代码路径。
 */
bool IsTypeSupportedByCStore(Oid typeOid)
{
    switch (typeOid) {
        // 支持的列存储数据类型
        case BOOLOID:
        case HLL_OID: // 与 BYTEA 类型相同
        case BYTEAOID:
        case CHAROID:
        case HLL_HASHVAL_OID: // 与 INT8 类型相同
        case INT8OID:
        case INT2OID:
        case INT4OID:
        case INT1OID:
        case NUMERICOID:
        case BPCHAROID:
        case VARCHAROID:
        case NVARCHAR2OID:
        case SMALLDATETIMEOID:
        case TEXTOID:
        case OIDOID:
        case FLOAT4OID:
        case FLOAT8OID:
        case ABSTIMEOID:
        case RELTIMEOID:
        case TINTERVALOID:
        case INETOID:
        case DATEOID:
        case TIMEOID:
        case TIMESTAMPOID:
        case TIMESTAMPTZOID:
        case INTERVALOID:
        case TIMETZOID:
        case CASHOID:
        case CIDROID:
        case BITOID:
        case VARBITOID:
        case CLOBOID:
        case BOOLARRAYOID: // 数组
        case HLL_ARRAYOID:
        case BYTEARRAYOID:
        case CHARARRAYOID:
        case HLL_HASHVAL_ARRAYOID:
        case INT8ARRAYOID:
        case INT2ARRAYOID:
        case INT4ARRAYOID:
        case INT1ARRAYOID:
        case ARRAYNUMERICOID:
        case BPCHARARRAYOID:
        case VARCHARARRAYOID:
        case NVARCHAR2ARRAYOID:
        case SMALLDATETIMEARRAYOID:
        case TEXTARRAYOID:
        case FLOAT4ARRAYOID:
        case FLOAT8ARRAYOID:
        case ABSTIMEARRAYOID:
        case RELTIMEARRAYOID:
        case ARRAYTINTERVALOID:
        case INETARRAYOID:
        case DATEARRAYOID:
        case TIMEARRAYOID:
        case TIMESTAMPARRAYOID:
        case TIMESTAMPTZARRAYOID:
        case ARRAYINTERVALOID:
        case ARRAYTIMETZOID:
        case CASHARRAYOID:
        case CIDRARRAYOID:
        case BITARRAYOID:
        case VARBITARRAYOID:
        case BYTEAWITHOUTORDERCOLOID:
        case BYTEAWITHOUTORDERWITHEQUALCOLOID:
            return true;
        default:
            break;
    }

    return false;
}

bool IsTypeSupportedByVectorEngine(Oid typeOid)
{
    // 如果类型受列存储支持，返回true
    if (IsTypeSupportedByCStore(typeOid)) {
        return true;
    }

    switch (typeOid) {
        /* Name、MacAddr 和 UUID 在 rowtovec 和 vectorow 中也会被处理，
         * 但这可能导致结果不正确。因此在这里不支持它们。
         */
        case VOIDOID:
        case UNKNOWNOID:
        case CSTRINGOID: {
            return true;
        }
        default:
            break;
    }

    ereport(DEBUG2, (errmodule(MOD_OPT_PLANNER),
        errmsg("由于不支持的类型，向量化计划失败：%u", typeOid)));

    return false;
}

/*
 * IsTypeSupportedByORCRelation
 * 如果类型受 ORC 格式关系支持，返回true
 */
bool IsTypeSupportedByORCRelation(_in_ Oid typeOid)
{
    // 我们不支持用户定义的类型
    if (typeOid >= FirstNormalObjectId) {
        return false;
    }

    // 支持的 ORC 格式关系数据类型
    static Oid supportType[] = {BOOLOID,
        OIDOID,
        INT8OID,
        INT2OID,
        INT4OID,
        INT1OID,
        NUMERICOID,
        CHAROID,
        BPCHAROID,
        VARCHAROID,
        NVARCHAR2OID,
        TEXTOID,
        CLOBOID,
        FLOAT4OID,
        FLOAT8OID,
        DATEOID,
        TIMESTAMPOID,
        INTERVALOID,
        TINTERVALOID,
        TIMESTAMPTZOID,
        TIMEOID,
        TIMETZOID,
        SMALLDATETIMEOID,
        CASHOID};
    if (DATEOID == typeOid && C_FORMAT == u_sess->attr.attr_sql.sql_compatibility) {
        ereport(ERROR,
            (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                errmodule(MOD_HDFS),
                errmsg("C格式数据库中不支持HDFS表的日期类型。")));
    }

    for (uint32 i = 0; i < sizeof(supportType) / sizeof(Oid); ++i) {
        if (supportType[i] == typeOid) {
            return true;
        }
    }
    return false;
}

/*
 * is_support_old_ts_style
 *
 * 检查旧版时间序列存储是否支持给定的键值类型 (kvtype) 和数据类型 (typeOid)。
 * 不同的键值类型有不同的支持数据类型，例如，ATT_KV_TAG 支持 TEXTOID 类型，
 * ATT_KV_FIELD 支持 NUMERICOID 和 TEXTOID 类型，ATT_KV_TIMETAG 支持 TIMESTAMPTZOID 和 TIMESTAMPOID 类型。
 *
 * 参数：
 *   - kvtype: 列是否为标签 (ATT_KV_TAG)、字段 (ATT_KV_FIELD)、时间标签 (ATT_KV_TIMETAG) 或隐藏标签 (ATT_KV_HIDE)
 *   - typeOid: 数据类型的 OID
 *
 * 返回值：
 *   如果支持给定的键值类型和数据类型，返回 true；否则返回 false。
 */
static bool is_support_old_ts_style(int kvtype, Oid typeOid)
{
    if (kvtype == ATT_KV_TAG || kvtype == ATT_KV_HIDE) {
        return typeOid == TEXTOID;
    } else if (kvtype == ATT_KV_FIELD) {
        return (typeOid == NUMERICOID || typeOid == TEXTOID);
    } else if (kvtype == ATT_KV_TIMETAG) {
        return (typeOid == TIMESTAMPTZOID || typeOid == TIMESTAMPOID);
    } else {
        /* 未识别的数据类型 */
        return false;
    }
}

/*
 * is_support_new_ts_style
 *
 * 检查新版时间序列存储是否支持给定的键值类型 (kvtype) 和数据类型 (typeOid)。
 * 新版支持的数据类型存储在 support_type 数组中，不同的键值类型有不同的支持数据类型。
 *
 * 参数：
 *   - kvtype: 列是否为标签 (ATT_KV_TAG)、字段 (ATT_KV_FIELD)、时间标签 (ATT_KV_TIMETAG) 或隐藏标签 (ATT_KV_HIDE)
 *   - typeOid: 数据类型的 OID
 *
 * 返回值：
 *   如果支持给定的键值类型和数据类型，返回 true；否则返回 false。
 */
static bool is_support_new_ts_style(int kvtype, Oid typeOid)
{
    static Oid support_type[] = {BOOLOID, INT8OID, INT4OID, NUMERICOID, BPCHAROID, TEXTOID, FLOAT4OID, FLOAT8OID};
    static Oid tag_support_type[] = {BOOLOID, INT8OID, INT4OID, BPCHAROID, TEXTOID};

    if (kvtype == ATT_KV_TAG) {
        for (uint32 i = 0; i < sizeof(tag_support_type) / sizeof(Oid); ++i) {
            if (tag_support_type[i] == typeOid) {
                return true;
            }
        }
        return false;
    } else if (kvtype == ATT_KV_FIELD) {
        for (uint32 i = 0; i < sizeof(support_type) / sizeof(Oid); ++i) {
            if (support_type[i] == typeOid) {
                return true;
            }
        }
        return false;
    } else if (kvtype == ATT_KV_TIMETAG) {
        return (typeOid == TIMESTAMPTZOID || typeOid == TIMESTAMPOID);
    } else if (kvtype == ATT_KV_HIDE) {
        /* hidetag 列仅支持 CHAROID 类型 */
        if (typeOid == CHAROID) {
            return true;
        } else {
            ereport(LOG, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED), errmsg("Invalid hide column type: %u", typeOid)));
            return false;
        }
    } else {
        /* 未识别的数据类型 */
        return false;
    }
}

/*
 * IsTypeSupportedByTsStore
 *
 * 用于时间序列存储。如果给定的键值类型和数据类型受到支持，则返回 true。
 * 对于标签，支持的类型为 TEXT；对于字段和标签，支持的类型为 NUMERIC、TEXT、BOOL、INT、FLOAT 和 DOUBLE。
 *
 * 参数：
 *   - kvtype: 列是否为标签 (ATT_KV_TAG)、字段 (ATT_KV_FIELD) 或时间标签 (ATT_KV_TIMETAG)
 *   - typeOid: 数据类型的 OID
 *
 * 返回值：
 *   如果支持给定的键值类型和数据类型，返回 true；否则返回 false。
 */
bool IsTypeSupportedByTsStore(_in_ int kvtype, _in_ Oid typeOid)
{
    const int support_type_number = 92257;

    if (pg_atomic_read_u32(&WorkingGrandVersionNum) >= support_type_number) {
        return is_support_new_ts_style(kvtype, typeOid);
    } else {
        return is_support_old_ts_style(kvtype, typeOid);
    }
}

/*
 * IsTypeSupportedByUStore
 *
 * 返回 true，如果给定的数据类型 (typeOid) 受到 UStore 的支持。
 * 不支持用户定义类型。
 *
 * 参数：
 *   - typeOid: 数据类型的 OID
 *   - typeMod: 类型修饰符
 *
 * 返回值：
 *   如果支持给定的数据类型，返回 true；否则返回 false。
 */
bool IsTypeSupportedByUStore(_in_ const Oid typeOid, _in_ const int32 typeMod)
{
    /* 不支持用户定义类型 */
    if (typeOid >= FirstNormalObjectId)
        return false;

    static Oid supportType[] = {
        BOOLOID, BYTEAOID, CHAROID, INT8OID, INT2OID, INT4OID, INT1OID, NUMERICOID, BPCHAROID,
        VARCHAROID, NVARCHAR2OID, SMALLDATETIMEOID, TEXTOID, OIDOID, FLOAT4OID, FLOAT8OID, ABSTIMEOID,
        RELTIMEOID, TINTERVALOID, INETOID, DATEOID, TIMEOID, TIMESTAMPOID, TIMESTAMPTZOID, INTERVALOID,
        TIMETZOID, CASHOID, CIDROID, BITOID, VARBITOID, NAMEOID, RAWOID, BLOBOID, CIRCLEOID, MACADDROID,
        UUIDOID, TSVECTOROID, TSQUERYOID, POINTOID, LSEGOID, BOXOID, PATHOID, POLYGONOID, INT4ARRAYOID
    };

    for (uint32 i = 0; i < sizeof(supportType) / sizeof(Oid); ++i) {
        if (supportType[i] == typeOid) {
            return true;
        }
    }

    return false;
}


/*
 * 检查类型是否在黑名单中。
 */
bool IsTypeInBlacklist(Oid typoid)
{
    bool isblack = false;

    switch (typoid) {
#ifdef ENABLE_MULTIPLE_NODES
        case XMLOID:
#endif /* ENABLE_MULTIPLE_NODES */
        case LINEOID:
        case PGNODETREEOID:
            isblack = true;
            break;
        default:
            break;
    }

    return isblack;
}

/*
 * 检查类型是否在安装组中。
 */
bool IsTypeTableInInstallationGroup(const Type type_tup)
{
    if (type_tup && !IsInitdb && IS_PGXC_COORDINATOR) {
        Form_pg_type typeForm = (Form_pg_type)GETSTRUCT(type_tup);
        char* groupname = NULL;
        Oid groupoid = InvalidOid;

        if (OidIsValid(typeForm->typrelid)) {
            char relkind = get_rel_relkind(typeForm->typrelid);
            if (RELKIND_VIEW != relkind && RELKIND_CONTQUERY != relkind) {
                groupoid = ng_get_baserel_groupoid(typeForm->typrelid, relkind);
            }

            if (OidIsValid(groupoid)) {
                groupname = get_pgxc_groupname(groupoid);
            }

            char* installation_groupname = PgxcGroupGetInstallationGroup();
            if (groupname != NULL && installation_groupname != NULL && strcmp(groupname, installation_groupname) != 0) {
                return false;
            }
        }
    }
    return true;
}

/*
 * 将包裹类型名转换为指定格式。
 */
char* CastPackageTypeName(const char* typName, Oid objOid, bool isPackage, bool isPublic)
{
    StringInfoData  castTypName;
    initStringInfo(&castTypName);

    /* 私有类型名在开头加 '$' */
    if (isPackage) {
        if (!isPublic) {
            appendStringInfoString(&castTypName, "$");
        }
    }

    /* 转换包裹或过程 oid */
    char* oidStr = NULL;
    const int oidStrLen = 12;
    oidStr = (char *)palloc0(oidStrLen * sizeof(char));
    pg_ltoa(objOid, oidStr);
    appendStringInfoString(&castTypName, oidStr);
    pfree_ext(oidStr);

    /* 转换类型名 */
    appendStringInfoString(&castTypName, ".");
    appendStringInfoString(&castTypName, typName);

    return castTypName.data;
}

/*
 * 解析类型名，返回去掉包裹 oid 后的类型名。
 */
char* ParseTypeName(const char* typName, Oid pkgOid)
{
    if (!OidIsValid(pkgOid)) {
        return NULL;
    }
    char* oldStr = NULL;
    const int oldStrLen  =12;
    oldStr = (char*)palloc0(oldStrLen * sizeof(char));
    pg_ltoa(pkgOid, oldStr);
    int len = strlen(oldStr);
    char* pos = strstr((char*)typName, oldStr);
    pfree_ext(oldStr);
    if (NULL == pos) {
        return NULL;
    }
    pos +=len;
    if (*pos != '.') {
        return NULL;
    }
    return pstrdup(++pos);
}

/*
 * 查找是否 %type 引用了包裹变量类型。
 */
HeapTuple FindPkgVariableType(ParseState* pstate, const TypeName* typname, int32* typmod_p,
    TypeDependExtend* depend_extend)
{
    HeapTuple tup = NULL;

#ifdef ENABLE_MULTIPLE_NODES
    return tup;
#else
    int32 typmod = -1;
    if (!enable_plpgsql_gsdependency_guc() && u_sess->plsql_cxt.curr_compile_context == NULL) {
        return tup;
    }

    /* 处理 var.col%TYPE */
    tup = FindRowVarColType(typname->names, NULL, NULL, typmod_p);
    if (tup != NULL) {
        return tup;
    }

    /* 查找 package.var%TYPE */
    if (list_length(typname->names) <= 1) {
        return tup;
    }
    if (list_length(typname->names) >= (enable_plpgsql_gsdependency_guc() ? 5 :4)) {
        return tup;
    }
    PLpgSQL_datum* datum = GetPackageDatum(typname->names);
    if (datum != NULL && datum->dtype == PLPGSQL_DTYPE_VAR) {
        Oid typOid =  ((PLpgSQL_var*)datum)->datatype->typoid;
        tup = SearchSysCache1(TYPEOID, ObjectIdGetDatum(typOid));
        /* 不应该发生 */
        if (!HeapTupleIsValid(tup)) {
            ereport(ERROR, (errcode(ERRCODE_CACHE_LOOKUP_FAILED),
                errmsg("cache lookup failed for type %u", typOid)));
        }
        typmod = typenameTypeMod(pstate, typname, (Type)tup);
        if (typmod_p != NULL) {
            *typmod_p = typmod;
        }
        if (enable_plpgsql_gsdependency() && NULL != depend_extend) {
            DeconstructQualifiedName(typname->names, &depend_extend->schemaName,
                                     &depend_extend->objectName, &depend_extend->packageName);
        }
    } else if (enable_plpgsql_undefined() && NULL != depend_extend) {
        Oid undefRefObjOid = gsplsql_try_build_exist_pkg_undef_var(typname->names);
        if (OidIsValid(undefRefObjOid)) {
            depend_extend->undefDependObjOid = undefRefObjOid;
            tup = SearchSysCache1(TYPEOID, ObjectIdGetDatum(UNDEFINEDOID));
            if (typmod_p != NULL) {
                *typmod_p = -1;
            }
        }
    }
    return tup;
#endif
}

/*
 * 检查记录类型中是否有嵌套的表索引类型。
 */
static void check_record_nest_tableof_index_type(const char* typeName, List* typeNames)
{
    PLpgSQL_datum* datum = NULL;
    if (typeName != NULL) {
        PLpgSQL_nsitem* ns = NULL;
        PLpgSQL_package* pkg = u_sess->plsql_cxt.curr_compile_context->plpgsql_curr_compile_package;
        ns = plpgsql_ns_lookup(pkg->public_ns, false, typeName, NULL, NULL, NULL);
        if (ns == NULL) {
            ns = plpgsql_ns_lookup(pkg->private_ns, false, typeName, NULL, NULL, NULL);
        }

        if (ns == NULL || ns->itemtype != PLPGSQL_NSTYPE_RECORD) {
            return ;
        }
        datum = pkg->datums[ns->itemno];
    } else {
        datum = GetPackageDatum(typeNames);
    }

    if (datum != NULL && datum->dtype == PLPGSQL_DTYPE_RECORD_TYPE) {
        PLpgSQL_rec_type* var_type = (PLpgSQL_rec_type*)datum;
        PLpgSQL_type* type = NULL;
        for (int i = 0; i < var_type->attrnum; i++) {
            type = var_type->types[i];
            if (type->ttype == PLPGSQL_TTYPE_SCALAR && OidIsValid(type->tableOfIndexType)) {
                ereport(ERROR,
                    (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("record nested table of index type do not support in out args")));
            }
        }
    }
}

/*
 * 查找给定类型是否为包类型
 * 参数:
 * - typeNames: 类型名列表
 * - typeName: 类型名
 * - pkgOid: 包的 OID
 * - namespaceId: 命名空间的 OID
 * 返回值:
 * - 找到的类型的 OID，如果未找到则为 InvalidOid
 */
Oid LookupTypeInPackage(List* typeNames, const char* typeName, Oid pkgOid, Oid namespaceId)
{
    Oid typOid = InvalidOid;
    char* castTypeName = NULL;

    /* 如果 pkgOid 无效，则尝试在当前编译包中查找类型 */
    if (!OidIsValid(pkgOid)) {
        /* 如果不是编译包，直接返回无效的 OID */
        if (u_sess->plsql_cxt.curr_compile_context == NULL ||
            u_sess->plsql_cxt.curr_compile_context->plpgsql_curr_compile_package == NULL) {
            return typOid;
        }

        pkgOid = u_sess->plsql_cxt.curr_compile_context->plpgsql_curr_compile_package->pkg_oid;

        /* 首先查找公共包类型 */
        castTypeName = CastPackageTypeName(typeName, pkgOid, true, true);
        typOid = TypenameGetTypidExtended(castTypeName, false);
        pfree_ext(castTypeName);

        /* 如果未找到，尝试查找私有包类型 */
        if (!OidIsValid(typOid)) {
            castTypeName = CastPackageTypeName(typeName, pkgOid, true, false);
            typOid = TypenameGetTypidExtended(castTypeName, false);
            pfree_ext(castTypeName);
        }

        if (OidIsValid(typOid)) {
            check_record_nest_tableof_index_type(typeName, NULL);
        }
        return typOid;
    }

    /* 如果 pkgOid 有效，首先查找给定包的公共类型 */
    castTypeName = CastPackageTypeName(typeName, pkgOid, true, true);

    if (OidIsValid(namespaceId)) {
        /* 在给定命名空间中查找类型 */
        typOid = GetSysCacheOid2(TYPENAMENSP, PointerGetDatum(castTypeName), ObjectIdGetDatum(namespaceId));
        if (!OidIsValid(typOid)) {
            typOid = TryLookForSynonymType(castTypeName, namespaceId);
        }
    } else {
        /* 在默认命名空间中查找类型 */
        typOid = TypenameGetTypidExtended(castTypeName, false);
    }

    pfree_ext(castTypeName);

    if (OidIsValid(typOid)) {
        bool pkgValid = true;
        if (enable_plpgsql_gsdependency_guc()) {
            pkgValid = GetPgObjectValid(pkgOid, OBJECT_TYPE_PKGSPEC);
        } 
        if (pkgValid) {
            // check_record_nest_tableof_index_type(NULL, typeNames);
        }
        return typOid;
    }

    /*
     * 查找私有包类型，如果编译包与给定包相同
     * 如果不是编译包，直接返回无效的 OID
     */
    if (u_sess->plsql_cxt.curr_compile_context == NULL ||
        u_sess->plsql_cxt.curr_compile_context->plpgsql_curr_compile_package == NULL) {
        return typOid;
    }

    /* 如果不是同一个包，返回 */
    if (pkgOid != u_sess->plsql_cxt.curr_compile_context->plpgsql_curr_compile_package->pkg_oid) {
        return typOid;
    }

    castTypeName = CastPackageTypeName(typeName, pkgOid, true, false);

    if (OidIsValid(namespaceId)) {
        /* 在给定命名空间中查找类型 */
        typOid = GetSysCacheOid2(TYPENAMENSP, PointerGetDatum(castTypeName), ObjectIdGetDatum(namespaceId));
        if (!OidIsValid(typOid)) {
            typOid = TryLookForSynonymType(castTypeName, namespaceId);
        }
    } else {
        /* 在默认命名空间中查找类型 */
        typOid = TypenameGetTypidExtended(castTypeName, false);
    }

    pfree_ext(castTypeName);

    return typOid;
}

/*
 * 判断给定类型是否为二进制类型
 * 参数:
 * - typid: 待判断的类型 OID
 * 返回值:
 * - 如果是二进制类型，返回 true，否则返回 false
 */
bool IsBinaryType(Oid typid)
{
    return ((typid) == BLOBOID ||
            (typid) == BYTEAOID);
}

/*
 * 检查类型是否支持多字符集
 * 参数:
 * - typid: 待检查的类型 OID
 * - allow_array: 是否允许数组类型
 */
void check_type_supports_multi_charset(Oid typid, bool allow_array)
{
    switch (typid) {
        case XMLOID:
        case JSONOID:
        case TSVECTOROID:
        case GTSVECTOROID:
        case TSQUERYOID:
        case RECORDOID:
        case HLL_OID:
        case HLL_HASHVAL_OID:
        case HLL_TRANS_OID:
            ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                errmsg("不支持数据类型 '%s' 的多字符集", get_typename(typid))));
        default:
            break;
    }

    if (!allow_array && type_is_array(typid)) {
        ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
            errmsg("不支持数据类型 '%s' 的多字符集", get_typename(typid))));
    }
}

/*
 * 获取类型元组的状态
 * 参数:
 * - typ: 待获取状态的类型元组
 * 返回值:
 * - 类型元组的状态
 */
TypeTupStatus GetTypeTupStatus(Type typ)
{
    if (HeapTupleIsValid(typ)) {
        return (UNDEFINEDOID == HeapTupleGetOid(typ) ? UndefineTypeTup : NormalTypeTup);
    }
    return InvalidTypeTup;
}


/* -------------------------------------------------------------------------
 *
 * parser.cpp
 *        Main entry point/driver for openGauss grammar
 *
 * Note that the grammar is not allowed to perform any table access
 * (since we need to be able to do basic parsing even while inside an
 * aborted transaction).  Therefore, the data structures returned by
 * the grammar are "raw" parsetrees that still need to be analyzed by
 * analyze.c and related files.
 *
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *      src/common/backend/parser/parser.cpp
 *
 * -------------------------------------------------------------------------
 */

#include "postgres.h"
#include "knl/knl_variable.h"
#include "nodes/parsenodes.h"

#include "parser/gramparse.h"
#include "parser/parser.h"

extern void resetOperatorPlusFlag();

static void resetIsTimeCapsuleFlag()
{
    u_sess->parser_cxt.isTimeCapsule = false; // 重置时间胶囊标志位
}

static void resetHasPartitionComment()
{
    u_sess->parser_cxt.hasPartitionComment = false; // 重置包含分区注释标志位
}

static void resetCreateFuncFlag()
{
    u_sess->parser_cxt.isCreateFuncOrProc = false; // 重置创建函数或过程标志位
}

static void resetForbidTruncateFlag()
{
    u_sess->parser_cxt.isForbidTruncate = false; // 重置禁止截断标志位
}

static void resetHasSetUservarFlag()
{
    u_sess->parser_cxt.has_set_uservar = false; // 重置包含用户变量设置标志位
}

/*
 * raw_parser
 *        给定一个字符串形式的查询，进行词法和语法分析。
 *
 * 返回一个原始（未经分析的）解析树列表。
 */
List* raw_parser(const char* str, List** query_string_locationlist)
{
    core_yyscan_t yyscanner;
    base_yy_extra_type yyextra;
    int yyresult;

    /* 重置 u_sess->parser_cxt.stmt_contains_operator_plus */
    resetOperatorPlusFlag();
    
    /* 重置 u_sess->parser_cxt.hasPartitionComment */
    resetHasPartitionComment();
    
    /* 重置 u_sess->parser_cxt.isTimeCapsule */
    resetIsTimeCapsuleFlag();

    /* 重置 u_sess->parser_cxt.isCreateFuncOrProc */
    resetCreateFuncFlag();

    /* 重置 u_sess->parser_cxt.isForbidTruncate */
    resetForbidTruncateFlag();

    /* 重置 u_sess->parser_cxt.has_set_uservar */
    resetHasSetUservarFlag();

    /* 初始化 flex 扫描器 */
    yyscanner = scanner_init(str, &yyextra.core_yy_extra, &ScanKeywords, ScanKeywordTokens);

    /* base_yylex() 只需要这么多初始化 */
    yyextra.lookahead_num = 0;

    /* 初始化 bison 解析器 */
    parser_init(&yyextra);

    /* 解析！*/
    yyresult = base_yyparse(yyscanner);

    /* 清理（释放内存）*/
    scanner_finish(yyscanner);

    if (yyresult) { /* 错误 */
        return NIL;
    }

    /* 获取多查询的位置列表通过 lex。*/
    if (query_string_locationlist != NULL) {
        *query_string_locationlist = yyextra.core_yy_extra.query_string_locationlist;

        /* 处理来自客户端的没有分号结束的查询。 */
        if (PointerIsValid(*query_string_locationlist) &&
            (size_t)lfirst_int(list_tail(*query_string_locationlist)) < (strlen(str) - 1)) {
            *query_string_locationlist = lappend_int(*query_string_locationlist, strlen(str));
        }
    }

    return yyextra.parsetree;
}

#define GET_NEXT_TOKEN_WITHOUT_YY()                                                      \
    do {                                                                                 \
        if (yyextra->lookahead_num != 0) {                                               \
            next_token = yyextra->lookahead_token[yyextra->lookahead_num - 1];           \
            lvalp->core_yystype = yyextra->lookahead_yylval[yyextra->lookahead_num - 1]; \
            *llocp = yyextra->lookahead_yylloc[yyextra->lookahead_num - 1];              \
            yyextra->lookahead_num--;                                                    \
        } else {                                                                         \
            next_token = core_yylex(&(lvalp->core_yystype), llocp, yyscanner);           \
        }                                                                                \
    } while (0)

#define GET_NEXT_TOKEN()                                                                 \
    do {                                                                                 \
        cur_yylval = lvalp->core_yystype;                                                \
        cur_yylloc = *llocp;                                                             \
        GET_NEXT_TOKEN_WITHOUT_YY();                                                     \
    } while (0)

#define SET_LOOKAHEAD_TOKEN()                               \

    do {                                                    \
        yyextra->lookahead_token[0] = next_token;           \
        yyextra->lookahead_yylval[0] = lvalp->core_yystype; \
        yyextra->lookahead_yylloc[0] = *llocp;              \
        yyextra->lookahead_num = 1;                         \
    } while (0)

/*
 * parser 和核心词法分析器 (scan.l 中的 core_yylex) 之间的中间过滤器。
 *
 * 需要此过滤器的原因是因为在某些情况下，标准 SQL 语法需要超过一个 token 的前瞻。
 * 我们通过在这里组合 token 来减少这些情况到一个 token 的前瞻，以保持语法为 LALR(1)。
 *
 * 使用过滤器比直接在 scan.l 中尝试识别多词标记更简单，因为我们必须允许单词之间的注释。
 * 此外，不清楚如何在不重新引入扫描器回溯的情况下进行，而这将比此过滤器层的性能更高的代价。
 *
 * 过滤器还提供了在 core_YYSTYPE 和 YYSTYPE 表示之间进行转换的便捷位置（它们实际上是相同的东西，但符号不同）。
 */
int base_yylex(YYSTYPE* lvalp, YYLTYPE* llocp, core_yyscan_t yyscanner)
{
    base_yy_extra_type* yyextra = pg_yyget_extra(yyscanner);
    int cur_token;
    int next_token;
    core_YYSTYPE cur_yylval;
    YYLTYPE cur_yylloc;

    /* 获取下一个 token —— 我们可能已经有了 */
    if (yyextra->lookahead_num != 0) {
        cur_token = yyextra->lookahead_token[yyextra->lookahead_num - 1];
        lvalp->core_yystype = yyextra->lookahead_yylval[yyextra->lookahead_num - 1];
        *llocp = yyextra->lookahead_yylloc[yyextra->lookahead_num - 1];
        yyextra->lookahead_num--;
    } else {
        cur_token = core_yylex(&(lvalp->core_yystype), llocp, yyscanner);
    }

    if (u_sess->attr.attr_sql.sql_compatibility == B_FORMAT && yyextra->lookahead_num == 0) {
        bool is_last_colon;
        if (cur_token == int(';')) {
            is_last_colon = true;
        } else {
            is_last_colon = false;
        }
        if (yyextra->core_yy_extra.is_delimiter_name == true) {
            if (strcmp(";",u_sess->attr.attr_common.delimiter_name) == 0) {
                cur_token = END_OF_INPUT_COLON;
            } else {
                if (yyextra->core_yy_extra.is_last_colon == false ) {
                    cur_token = END_OF_INPUT_COLON;
                } else {
                    cur_token = END_OF_INPUT;
                }
            }
        }
        if (yyextra->core_yy_extra.is_proc_end == true) {
            cur_token = END_OF_PROC;
        }
        yyextra->core_yy_extra.is_proc_end = false;
        yyextra->core_yy_extra.is_delimiter_name = false;
        yyextra->core_yy_extra.is_last_colon = is_last_colon;
    }
    
    /* 是否需要向前查看可能的多词标记？ */
    switch (cur_token) {
        case NULLS_P:
            /*
             * NULLS FIRST and NULLS LAST must be reduced to one token
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case FIRST_P:
                    cur_token = NULLS_FIRST;
                    break;
                case LAST_P:
                    cur_token = NULLS_LAST;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case NOT:
            /*
             * @hdfs
             *  为了解决 gram.y 中的冲突，NOT 和 ENFORCED 必须被合并为一个 token。
             */
            GET_NEXT_TOKEN();

            switch (next_token) {
                case ENFORCED:
                    cur_token = NOT_ENFORCED;
                    break;
                case IN_P:
                    cur_token = NOT_IN;
                    break;
                case BETWEEN:
                    cur_token = NOT_BETWEEN;
                    break;
                case LIKE:
                    cur_token = NOT_LIKE;
                    break;
                case ILIKE:
                    cur_token = NOT_ILIKE;
                    break;
                case SIMILAR:
                    cur_token = NOT_SIMILAR;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();

                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case EVENT:
            /*
             * Event trigger 必须被合并为一个 token
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case TRIGGER:
                    cur_token = EVENT_TRIGGER;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();

                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;
        case WITH:
            /*
             * WITH TIME 必须被合并为一个 token
             */
            GET_NEXT_TOKEN();

            switch (next_token) {
                case TIME:
                    cur_token = WITH_TIME;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();

                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case INCLUDING:

            /*
             * INCLUDING ALL 必须被合并为一个 token
             */
            GET_NEXT_TOKEN();

            switch (next_token) {
                case ALL:
                    cur_token = INCLUDING_ALL;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();

                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case RENAME:

            /*
             * RENAME PARTITION 必须被合并为一个 token
             */
            GET_NEXT_TOKEN();

            switch (next_token) {
                case PARTITION:
                    cur_token = RENAME_PARTITION;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case PARTITION:

            /*
             * RENAME PARTITION 必须被合并为一个 token
             */
            GET_NEXT_TOKEN();

            switch (next_token) {
                case FOR:
                    cur_token = PARTITION_FOR;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;
        case SUBPARTITION:

            GET_NEXT_TOKEN();

            switch (next_token) {
                case FOR:
                    cur_token = SUBPARTITION_FOR;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;
        case ADD_P:
            /*
             * ADD PARTITION 必须被合并为一个 token
             */
            GET_NEXT_TOKEN();

            switch (next_token) {
                case PARTITION:
                    cur_token = ADD_PARTITION;
                    break;
                case SUBPARTITION:
                    cur_token = ADD_SUBPARTITION;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;
        case DROP:
            /*
             * DROP PARTITION must be reduced to one token
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case PARTITION:
                    cur_token = DROP_PARTITION;
                    break;
                case SUBPARTITION:
                    cur_token = DROP_SUBPARTITION;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case REBUILD:
            /*
             * REBUILD PARTITION must be reduced to one token
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case PARTITION:
                    cur_token = REBUILD_PARTITION;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case MODIFY_P:
            /*
             * MODIFY PARTITION must be reduced to one token
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case PARTITION:
                    cur_token = MODIFY_PARTITION;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case DECLARE:
            /*
             * DECLARE foo CUROSR must be looked ahead, and if determined as a DECLARE_CURSOR, we should set the yylaval
             * and yylloc back, letting the parser read the cursor name correctly.
             * here we may still have token in lookahead_token, so use GET_NEXT_TOKEN to get
             */
            GET_NEXT_TOKEN();
            /* 获取 DECLARE 后的第一个 token，我们不关心它是什么 */
            yyextra->lookahead_token[1] = next_token;
            yyextra->lookahead_yylval[1] = lvalp->core_yystype;
            yyextra->lookahead_yylloc[1] = *llocp;

            /* 
             * 获取 DECLARE 后的第二个 token。如果是 cursor 语法，我们确定这是一个 cursor 语句
             * 事实上，我们确保这里没有任何前瞻的 token，因为 MAX_LOOKAHEAD_NUM 是 2。
             * 但有一天 MAX_LOOKAHEAD_NUM 变大了，所以我们仍然使用 GET_NEXT_TOKEN_WITHOUT_SET_CURYY
             */
            GET_NEXT_TOKEN_WITHOUT_YY();
            yyextra->lookahead_token[0] = next_token;
            yyextra->lookahead_yylval[0] = lvalp->core_yystype;
            yyextra->lookahead_yylloc[0] = *llocp;
            yyextra->lookahead_num = 2;

            switch (next_token) {
                case CURSOR:
                case BINARY:
                case INSENSITIVE:
                case NO:
                case SCROLL:
                    cur_token = DECLARE_CURSOR;
                    /* 并将输出信息回退到 cur_token，因为我们应该正确读取游标名称。 */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
                default:
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case VALID:
            /*
             * VALID BEGIN must be reduced to one token, to avoid conflict with BEGIN TRANSACTIOn and BEGIN anonymous
             * block.
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case BEGIN_P:
                case BEGIN_NON_ANOYBLOCK:
                    cur_token = VALID_BEGIN;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case START:
            /*
             * START WITH must be reduced to one token, to allow START as table / column alias.
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case WITH:
                    cur_token = START_WITH;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case CONNECT:
            /*
             * CONNECT BY must be reduced to one token, to allow CONNECT as table / column alias.
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case BY:
                    cur_token = CONNECT_BY;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

         case ON:
            /* 在这里我们可能仍然有前瞻的 token，所以使用 GET_NEXT_TOKEN 来获取 */
            GET_NEXT_TOKEN();
            /* 获取 ON 后的第一个 token（普通 UPDATE 语句）。我们不关心它是什么 */
            yyextra->lookahead_token[1] = next_token;
            yyextra->lookahead_yylval[1] = lvalp->core_yystype;
            yyextra->lookahead_yylloc[1] = *llocp;

            /*
             * 获取 ON 后的第二个 token。
             * 事实上，我们确保这里没有任何前瞻的 token，因为 MAX_LOOKAHEAD_NUM 是 2。
             * 但有一天 MAX_LOOKAHEAD_NUM 变大了，所以我们仍然使用 GET_NEXT_TOKEN_WITHOUT_SET_CURYY
             */
            GET_NEXT_TOKEN_WITHOUT_YY();
            yyextra->lookahead_token[0] = next_token;
            yyextra->lookahead_yylval[0] = lvalp->core_yystype;
            yyextra->lookahead_yylloc[0] = *llocp;
            yyextra->lookahead_num = 2;

            switch (next_token) {
                case CURRENT_TIMESTAMP:
                case CURRENT_TIME:
                case CURRENT_DATE:
                case LOCALTIME:
                case LOCALTIMESTAMP:
                    cur_token = ON_UPDATE_TIME;
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
                default:
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case SHOW:
            /*
             * SHOW ERRORS must be reduced to one token, to allow ERRORS as table / column alias.
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case ERRORS:
                    cur_token = SHOW_ERRORS;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case USE_P:
            /*
             * USE INDEX \USE KEY must be reduced to one token, to allow KEY\USE as table / column alias.
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case KEY:
                    cur_token = USE_INDEX;
                    break;
                case INDEX:
                    cur_token = USE_INDEX;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case FORCE:
            /*
             * FORCE INDEX \FORCE KEY must be reduced to one token, to allow KEY\FORCE as table / column alias.
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case KEY:
                    cur_token = FORCE_INDEX;
                    break;
                case INDEX:
                    cur_token = FORCE_INDEX;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        case IGNORE:
            /*
             * IGNORE INDEX \IGNORE KEY must be reduced to one token, to allow KEY\IGNORE as table / column alias.
             */
            GET_NEXT_TOKEN();
            switch (next_token) {
                case KEY:
                case INDEX:
                    cur_token = IGNORE_INDEX;
                    break;
                default:
                    /* 保存前瞻的 token 以备下次使用 */
                    SET_LOOKAHEAD_TOKEN();
                    /* 并将输出信息回退到 cur_token */
                    lvalp->core_yystype = cur_yylval;
                    *llocp = cur_yylloc;
                    break;
            }
            break;

        default:

            break;
    }

    return cur_token;
}

/*
 * @Description: 检查是否是只包含注释和分号的空查询。
 * @Param query_string: 需要检查的查询字符串。
 * @return: 是 true，否 false。
 */
static bool is_empty_query(char* query_string)
{
    char begin_comment[3] = "/*";
    char end_comment[3] = "*/";
    char empty_query[2] = ";";
    char* end_comment_position = NULL;

    /* 去除字符串开头的所有空格。*/
    while (isspace((unsigned char)*query_string)) {
        query_string++;
    }

    /* 从查询字符串的开头去除所有的注释。*/
    while (strncmp(query_string, begin_comment, 2) == 0) {
        /*
         * 由于查询字符串经过解析，每当它包含 begin_comment 时，
         * 它将包含 end_comment，end_comment_position 在这里不能为 null。
         */
        end_comment_position = strstr(query_string, end_comment);
        query_string = end_comment_position + 2;
        while (isspace((unsigned char)*query_string)) {
            query_string++;
        }
    }

    /* 检查查询字符串是否为空查询。*/
    if (strcmp(query_string, empty_query) == 0) {
        return true;
    } else {
        return false;
    }
}

/*
 * @Description: 将查询字符串拆分为单独的单一查询。
 * @Param [IN] query_string_single: 存储拆分后的单一查询的数组。
 * @Param [IN] query_string: 包含多个语句的初始查询字符串。
 * @Param [IN] query_string_locationList: 从词法分析器获取的记录单一查询终止位置（分号位置）的列表。
 * @Param [IN] stmt_num: 表示多查询中的第 n 个单一查询。
 * @return [IN/OUT] query_string_single: 存储单一查询的指针数组。
 * @NOTICE: 调用方负责释放此处分配的内存。
 */
char** get_next_snippet(
    char** query_string_single, const char* query_string, List* query_string_locationlist, int* stmt_num)
{
    int query_string_location_start = 0;
    int query_string_location_end = -1;
    char* query_string_single_p = NULL;
    int single_query_string_len = 0;

    int stmt_count = list_length(query_string_locationlist);

    /* 为单一查询的第一次分配内存。*/
    if (query_string_single == NULL) {
        query_string_single = (char**)palloc0(sizeof(char*) * stmt_count);
    }

    /*
     * 获取多查询的片段，直到获取非空查询为止，因为空查询字符串无需处理。
     */
    for (; *stmt_num < stmt_count;) {
        /*
         * 注意：locationlist 只存储每个单一查询的结束位置，而没有任何开始位置。
         */
        if (*stmt_num == 0) {
            query_string_location_start = 0;
        } else {
            query_string_location_start = list_nth_int(query_string_locationlist, *stmt_num - 1) + 1;
        }
        query_string_location_end = list_nth_int(query_string_locationlist, (*stmt_num)++);

        /* 为每个单一查询字符串分配内存。*/
        single_query_string_len = query_string_location_end - query_string_location_start + 1;
        query_string_single[*stmt_num - 1] = (char*)palloc0(sizeof(char) * (single_query_string_len + 1));

        /* 将 query_string_location_start 和 query_string_location_end 之间的查询字符串复制到 query_string_single。*/
        query_string_single_p = query_string_single[*stmt_num - 1];
        while (query_string_location_start <= query_string_location_end) {
            *query_string_single_p = *(query_string + query_string_location_start);
            query_string_location_start++;
            query_string_single_p++;
        }

        /*
         * 如果 query_string_single 是只包含注释或空字符串的空查询，
         * 则跳过它。
         * 否则，退出循环。
         */
        if (is_empty_query(query_string_single[*stmt_num - 1])) {
            continue;
        } else {
            break;
        }
    }

    return query_string_single;
}

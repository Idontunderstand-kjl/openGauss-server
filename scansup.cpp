/* -------------------------------------------------------------------------
 *
 * scansup.cpp
 *	  support routines for the lex/flex scanner, used by both the normal
 * backend as well as the bootstrap backend
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/common/backend/parser/scansup.cpp
 *
 * -------------------------------------------------------------------------
 */
#include "postgres.h"
#include "knl/knl_variable.h"

#include <ctype.h>

#include "parser/scansup.h"
#include "mb/pg_wchar.h"

/* ----------------
 *		scanstr
 *
 * 如果传入的字符串具有转义代码，将转义代码映射为实际字符
 *
 * 返回的字符串是通过 palloc 分配的，调用者最终应该通过 pfree 进行释放!
 * ----------------
 */
char* scanstr(const char* s)
{
    char* newStr = NULL;
    int len, i, j;

    if (s == NULL || s[0] == '\0')
        return pstrdup("");

    len = strlen(s);

    newStr = (char*)palloc(len + 1); /* 字符串长度不会变长 */

    for (i = 0, j = 0; i < len; i++) {
        if (s[i] == '\'') {
            /*
             * 注意：如果扫描器正常工作，未转义的引号只能成对出现，所以应该有另一个字符。
             */
            i++;
            newStr[j] = s[i];
        } else if (s[i] == '\\') {
            i++;
            switch (s[i]) {
                case 'b':
                    newStr[j] = '\b';
                    break;
                case 'f':
                    newStr[j] = '\f';
                    break;
                case 'n':
                    newStr[j] = '\n';
                    break;
                case 'r':
                    newStr[j] = '\r';
                    break;
                case 't':
                    newStr[j] = '\t';
                    break;
                case '0':
                case '1':
                case '2':
                case '3':
                case '4':
                case '5':
                case '6':
                case '7': {
                    int k;
                    unsigned long octVal = 0;

                    for (k = 0; s[i + k] >= '0' && s[i + k] <= '7' && k < 3; k++){
                        octVal = (octVal << 3) + (s[i + k] - '0');
                    }     
                    i += k - 1;
                    newStr[j] = ((char)octVal);
                } break;
                default:
                    newStr[j] = s[i];
                    break;
            } /* switch */
        } /* s[i] == '\\' */
        else {
            newStr[j] = s[i];
        }
        j++;
    }
    newStr[j] = '\0';
    return newStr;
}

/*
 * downcase_truncate_identifier() --- 对未引用标识符进行适当的小写和截断。可选择截断时发出警告。
 *
 * 返回一个包含调整后标识符的 palloc'd 字符串。
 *
 * 注意：在某些用法中，传递的字符串可能没有以 null 结尾。
 *
 * 注意：此函数的 API 被设计为允许小写转换增加字符串长度，但我们目前还不支持这一点。
 * 如果要实现它，您需要修复 utils/adt/varlena.c 中的 SplitIdentifierString()。
 */
char* downcase_truncate_identifier(const char* ident, int len, bool warn)
{
    char* result = NULL;
    int i;
    bool enc_is_single_byte = false;

    result = (char*)palloc(len + 1);
    enc_is_single_byte = pg_database_encoding_max_length() == 1;

    /*
     * SQL99规定要进行 Unicode-aware 大小写规范化，但我们尚未为此提供基础设施。
     * 相反，我们使用 tolower() 提供区域设置感知的翻译。
     * 但是，在某些情况下，这也不正确（例如，土耳其语可能会对 'i' 和 'I' 进行奇怪的处理）。
     * 我们目前的妥协是对具有高位设置的字符使用 tolower()，只要它们不是多字节字符的一部分，并且对于 7 位字符使用 ASCII-only 小写。
     */
    for (i = 0; i < len; i++) {
        unsigned char ch = (unsigned char)ident[i];

        if (ch >= 'A' && ch <= 'Z') {
            ch += 'a' - 'A';
		} else if (enc_is_single_byte && IS_HIGHBIT_SET(ch) && isupper(ch)) {
            ch = tolower(ch);
		}
        result[i] = (char)ch;
    }
    result[i] = '\0';

    if (i >= NAMEDATALEN)
        truncate_identifier(result, i, warn);

    return result;
}

/*
 * truncate_identifier() --- 将标识符截断为 NAMEDATALEN-1 字节。
 *
 * 如果需要，给定的字符串会被修改。如果需要，会发出警告。
 *
 * 我们要求调用者传入字符串长度，因为在某些常见的用法中，这样可以节省 strlen() 调用。
 */
void truncate_identifier(char* ident, int len, bool warn)
{
    if (len >= NAMEDATALEN) {
        len = pg_mbcliplen(ident, len, NAMEDATALEN - 1);
        if (warn) {
            /*
             * 我们避免在这里使用 %.*s，因为如果数据在 libc 认为是当前编码的情况下无效，它可能会表现不当。
             */
            char buf[NAMEDATALEN];
            errno_t rc;

            rc = memcpy_s(buf, NAMEDATALEN, ident, len);
            securec_check(rc, "\0", "\0");
            buf[len] = '\0';
            ereport(NOTICE,
                (errcode(ERRCODE_NAME_TOO_LONG), errmsg("identifier \"%s\" will be truncated to \"%s\"", ident, buf)));
        }
        ident[len] = '\0';
    }
}

/*
 * scanner_isspace() --- 如果 Flex 扫描器将字符视为空格，则返回 TRUE
 *
 * 在重要的情况下，这应该用于匹配词法分析器的行为，而不是可能具有地区相关性的 isspace() 函数。
 *
 * 原则上，我们可能需要类似于 isalnum 等的函数，但目前只需要 isspace。
 */
bool scanner_isspace(char ch)
{
    /* 这必须与 scan.l 中的 {space} 字符列表匹配 */
    if (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' || ch == '\f') {
        return true;
    }

    return false;
}


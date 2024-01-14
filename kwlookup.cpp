/* -------------------------------------------------------------------------
 *
 * kwlookup.cpp
 *	  在openGauss中查找关键字的词法令牌
 *
 * NB - 此文件也被 ECPG 和 src/bin/ 中的几个前端程序使用，包括 pg_dump 和 psql
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/common/backend/parser/kwlookup.cpp
 *
 * -------------------------------------------------------------------------
 */

/* 使用 c.h，以便可以构建为前端或后端 */
#include "c.h"

#include <ctype.h>

#include "parser/kwlookup.h"

/*
 * ScanKeywordLookup - 查看给定的单词是否是关键字
 *
 * 返回指向ScanKeyword表项的指针，如果没有匹配则返回NULL。
 *
 * 进行大小写不敏感的匹配。请注意，我们故意使用简化的大小写转换，只会将 'A'-'Z' 转换为 'a'-'z'，
 * 即使我们处于 tolower() 会产生更多或不同转换的区域设置。这是为了遵循 SQL99 规范，
 * 该规范规定关键字应以这种方式匹配，即使非关键字标识符接收不同的大小写标准化映射。
 */
int ScanKeywordLookup(const char *str, const ScanKeywordList *keywords)
{
	size_t len;
	int	h;
	const char *kw;

	/*
	 * 如果字符串太长而不能成为任何关键字，则立即拒绝。这样可以节省在长字符串上无用的哈希和小写转换工作。
	 */
	len = strlen(str);
	if (len > (size_t)keywords->max_kw_len)
		return -1;

	/*
	 * 计算哈希函数。我们假设它是为产生不区分大小写的结果而生成的。
	 * 由于它是一个完美的哈希，我们只需要匹配它标识的特定关键字。
	 */
	h = keywords->hash(str, len);
	/* 超出范围的结果意味着没有匹配 */
	if (h < 0 || h >= keywords->num_keywords)
		return -1;

	/*
	 * 逐个字符比较，看是否有匹配项，对输入字符进行 ASCII-only 的小写转换。
	 * 我们不能使用 tolower()，因为在某些区域设置（例如土耳其语）中，它可能产生错误的翻译。
	 */
	kw = GetScanKeyword(h, keywords);
	while (*str != '\0') {
		char ch = *str++;
		if (ch >= 'A' && ch <= 'Z')
			ch += 'a' - 'A';
		if (ch != *kw++)
			return -1;
	}
	if (*kw != '\0')
		return -1;

	/* 成功！ */
	return h;
}

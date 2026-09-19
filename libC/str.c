#include <string.h>
#include <gc.h>

#include "str.h"

value string_concat(value s1, value s2) {
	const char *a = (const char*)s1;
	const char *b = (const char*)s2;
	size_t la = strlen(a);
	size_t lb = strlen(b);
	char *buf = (char*)GC_MALLOC(la + lb + 1);
	memcpy(buf, a, la);
	memcpy(buf + la, b, lb + 1);
	return (value)buf;
}

#include "runtime.h"
#include "stdlib_list.h"

static inline value _core_list_length(value cls, value l) {
	(void)cls;
	int64_t n = 0;
#if defined(EAGER) || defined(STATIC)
	lst *p = (lst*)l;
	while (p != NULL) {
		n++;
		p = (lst*)p->t;
	}
#else
	lst *p = (lst*)l;
	while (!is_NULL(p)) {
		n++;
		p = (lst*)tl(p);
	}
#endif
	return (value)n;
}
DEF_UNARY(list_length, _core_list_length)

STDLIB_LIST_UNARY_LIST(STDLIB_TABLE)

STDLIB_LIST_UNARY_LIST(STDLIB_EXPORT)

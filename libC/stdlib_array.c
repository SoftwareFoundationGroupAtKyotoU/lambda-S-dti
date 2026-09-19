#include "runtime.h"
#include "stdlib_array.h"

static inline value _core_array_to_list(value cls, value a) {
	(void)cls;
#if defined(MONOTONIC) || defined(STATIC)
	uint32_t n = ((arr_raw*)a)->length;
#else
	uint32_t n = (uint32_t)length((arr*)a);
#endif
	value acc = 0; // nil
	for (int64_t i = (int64_t)n - 1; i >= 0; i--) {
#if defined(MONOTONIC) || defined(STATIC)
		value elem = ((arr_raw*)a)->vs[i];
#else
		value elem = get((arr*)a, (uint32_t)i);
#endif
		lst *cell = (lst*)GC_MALLOC(sizeof(lst));
		cell->h = elem;
		cell->t = acc;
		acc = (value)cell;
	}
	return acc;
}
DEF_UNARY(array_to_list, _core_array_to_list)

STDLIB_ARRAY_UNARY_LIST(STDLIB_TABLE)

STDLIB_ARRAY_UNARY_LIST(STDLIB_EXPORT)

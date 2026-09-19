#include "runtime.h"
#include "stdlib_array.h"

/* ---- local array read helpers ---- */

static inline uint32_t _arr_length(value a) {
#if defined(MONOTONIC) || defined(STATIC)
	return ((arr_raw*)a)->length;
#else
	return (uint32_t)length((arr*)a);
#endif
}

static inline value _arr_get(value a, uint32_t i) {
#if defined(MONOTONIC) || defined(STATIC)
	return ((arr_raw*)a)->vs[i];
#else
	return get((arr*)a, i);
#endif
}

/* ---- core implementations ---- */

static inline value _core_array_to_list(value cls, value a) {
	(void)cls;
	uint32_t n = _arr_length(a);
	value acc = 0; // nil
	for (int64_t i = (int64_t)n - 1; i >= 0; i--) {
		lst *cell = (lst*)GC_MALLOC(sizeof(lst));
		cell->h = _arr_get(a, (uint32_t)i);
		cell->t = acc;
		acc = (value)cell;
	}
	return acc;
}
DEF_UNARY(array_to_list, _core_array_to_list)

static void _core_array_iteri_go(value f, value a, uint32_t i, uint32_t n) {
	if (i >= n) return;
	CALL1(CALL1(f, (value)i), _arr_get(a, i));
	_core_array_iteri_go(f, a, i + 1, n);
}
static inline value _core_array_iteri_x(value cls, value a) {
	value f = (value)((fun*)cls)->env[0];
	_core_array_iteri_go(f, a, 0, _arr_length(a));
	return 0;
}
DEF_UNARY(array_iteri_x, _core_array_iteri_x)
DEF_BINARY(array_iteri)

STDLIB_ARRAY_UNARY_LIST(STDLIB_TABLE)
STDLIB_ARRAY_BINARY_LIST(STDLIB_TABLE)

STDLIB_ARRAY_UNARY_LIST(STDLIB_EXPORT)
STDLIB_ARRAY_BINARY_LIST(STDLIB_EXPORT)

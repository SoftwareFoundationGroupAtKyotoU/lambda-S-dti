#if !defined(STATIC) && !defined(MONOTONIC)
#include <stdlib.h>
#include "arr.h"
#include "capp.h"
#include "ty.h"
#include "crc.h"

value get(arr *a, uint32_t i) {
	if (((arr_header*)a)->wrap) {
		#ifdef CAST
		ty *u1 = (ty*)((arr_wrap*)a)->u1;
		ty *u2 = (ty*)((arr_wrap*)a)->u2;
		return cast(get(((arr_wrap*)a)->w, i), u1->tydat.tyarray, u2->tydat.tyarray, a->rid, a->polarity);
		#else
		BOUNDS_CHECK(((arr_wrap*)a)->w, (int32_t)i);
		return apply_coerce(((arr_raw*)((arr_wrap*)a)->w)->vs[i], ((arr_wrap*)a)->c1);
		#endif
	} else {
		BOUNDS_CHECK(a, (int32_t)i);
		return ((arr_raw*)a)->vs[i];
	}
}

void put(arr *a, uint32_t i, value v) {
	if (((arr_header*)a)->wrap) {
		#ifdef CAST
		ty *u1 = (ty*)((arr_wrap*)a)->u1;
		ty *u2 = (ty*)((arr_wrap*)a)->u2;
		value casted = cast(v, u2->tydat.tyarray, u1->tydat.tyarray, a->rid, a->polarity ^ 1);
		put(((arr_wrap*)a)->w, i, casted);
		#else
		value coerced = apply_coerce(v, ((arr_wrap*)a)->c2);
		BOUNDS_CHECK(((arr_wrap*)a)->w, (int32_t)i);
		((arr_raw*)((arr_wrap*)a)->w)->vs[i] = coerced;
		#endif
	} else {
		BOUNDS_CHECK(a, (int32_t)i);
		((arr_raw*)a)->vs[i] = v;
	}
}

value length(arr *a) {
	if (((arr_header*)a)->wrap) {
		#ifdef CAST
		return length(((arr_wrap*)a)->w);
		#else
		return ((arr_raw*)((arr_wrap*)a)->w)->length;
		#endif
	} else {
		return ((arr_raw*)a)->length;
	}
}

#endif
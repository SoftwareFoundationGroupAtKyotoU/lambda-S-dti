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
		return toplevel_coerce(((arr_raw*)((arr_wrap*)a)->w)->vs[i], ((arr_wrap*)a)->c1);
		#endif
	} else {
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
		value coerced = toplevel_coerce(v, ((arr_wrap*)a)->c2);
		((arr_raw*)((arr_wrap*)a)->w)->vs[i] = coerced;
		#endif
	} else {
		((arr_raw*)a)->vs[i] = v;
	}
}

#endif
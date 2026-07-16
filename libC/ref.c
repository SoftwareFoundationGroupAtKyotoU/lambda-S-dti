#if !defined(STATIC) && !defined(MONOTONIC)
#include <stdlib.h>
#include "ref.h"
#include "capp.h"
#include "ty.h"
#include "crc.h"

static inline uintptr_t is_wrapped(ref* r) {
	#ifdef CAST
	return r->u1_tag & 0b1;
	#else
	return r->c_tag & 0b1;
	#endif
}

static inline uintptr_t erase_1bit_tag(uintptr_t x) {
	return x & ~0b1;
}

value deref(ref *r) {
	if (is_wrapped(r)) {
		#ifdef CAST
		ty *u1 = (ty*)erase_1bit_tag(r->u1_tag);
		ty *u2 = (ty*)erase_1bit_tag(r->u2_p);
		return cast(deref(r->w), u1->tydat.tyref, u2->tydat.tyref, r->rid, r->u2_p & 0b1);
		#else
		return toplevel_coerce(r->w->v, ((crc*)erase_1bit_tag(r->c_tag))->crcdat.ref_crc.c1);
		#endif
	} else {
		return r->v;
	}
}

void subst(ref *r, value v) {
	if (is_wrapped(r)) {
		#ifdef CAST
		ty *u1 = (ty*)erase_1bit_tag(r->u1_tag);
		ty *u2 = (ty*)erase_1bit_tag(r->u2_p);
		value casted = cast(v, u2->tydat.tyref, u1->tydat.tyref, r->rid, (r->u2_p & 0b1) ^ 1);
		subst(r->w, casted);
		#else
		value coerced = toplevel_coerce(v, ((crc*)erase_1bit_tag(r->c_tag))->crcdat.ref_crc.c2);
		r->w->v = coerced;
		#endif
	} else {
		r->v = v;
	}
}

#endif
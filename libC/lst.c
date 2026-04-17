#if !defined(EAGER) && !defined(STATIC)
#include <stdlib.h>
#include "lst.h"
#include "capp.h"
#include "ty.h"
#include "crc.h"

static inline uintptr_t is_wrapped(lst* l) {
	return l->t & 0b1;
}

static inline uintptr_t erase_1bit_tag(uintptr_t x) {
	return x & ~0b1;
}

int is_NULL(lst *l) {
	while (l != NULL && is_wrapped(l)) {
		l = l->w;
	}
	return (l == NULL);
}

value hd(lst *l) {
	if (is_wrapped(l)) {
		#ifdef CAST
		ty *u1 = (ty*)erase_1bit_tag(l->wrap_info.u1_tag);
		ty *u2 = (ty*)erase_1bit_tag(l->wrap_info.u2_p);
		return cast(hd(l->w), u1->tydat.tylist, u2->tydat.tylist, l->wrap_info.rid, l->wrap_info.u2_p & 0b1);
		#else
		return coerce(l->w->h, ((crc*)erase_1bit_tag(l->c_tag))->crcdat.lst_crc);
		#endif
	} else {
		return l->h;
	}
}

value tl(lst *l) {
	if (is_wrapped(l)) {
		#ifdef CAST
		ty *u1 = (ty*)erase_1bit_tag(l->wrap_info.u1_tag);
		ty *u2 = (ty*)erase_1bit_tag(l->wrap_info.u2_p);
		return cast(tl(l->w), u1, u2, l->wrap_info.rid, l->wrap_info.u2_p & 0b1);
		#else
		return coerce(l->w->t, (crc*)erase_1bit_tag(l->c_tag));
		#endif
	} else {
		return l->t;
	}
}

#endif
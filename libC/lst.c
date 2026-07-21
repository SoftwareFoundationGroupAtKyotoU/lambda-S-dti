#if !defined(EAGER) && !defined(STATIC)
#include <stdlib.h>
#include <gc.h>
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
		return toplevel_coerce(l->w->h, (crc*)erase_1bit_tag(l->c_tag));
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
		// The tail is itself a list, not a single element: applying the bare element
		// coercion s to it directly is a shape mismatch. It needs [s] applied to the
		// tail, and the tail may already be independently wrapped with its own
		// coercion -- so this inlines the same already-wrapped/compose-or-fresh-wrap
		// logic coerce()'s C_LIST case uses, working directly with the element
		// coercion instead of allocating a throwaway C_LIST wrapper around it.
		crc *s_elem = (crc*)erase_1bit_tag(l->c_tag);
		lst *rest = (lst*)l->w->t;
		lst *w;
		crc *c;
		if (rest != NULL && (rest->c_tag & 0b1)) { // the tail is itself already wrapped
			w = rest->w;
			c = compose((crc*)erase_1bit_tag(rest->c_tag), s_elem);
			if (c == &crc_id) return (value)w;
		} else {
			w = rest;
			c = s_elem;
		}
		value retv = (value)GC_MALLOC(sizeof(lst));
		((lst*)retv)->w = w;
		((lst*)retv)->c_tag = (uintptr_t)c | 0b1;
		return retv;
		#endif
	} else {
		return l->t;
	}
}

#endif
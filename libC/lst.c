#include <stdio.h>
#include <stdlib.h>

__attribute__((noreturn)) void did_not_match() {
	printf("didn't match");
	exit(1);
}

#if !defined(EAGER) && !defined(STATIC)
#include "lst.h"
#include "capp.h"
#include "ty.h"
#include "crc.h"

#ifdef CAST
int is_NULL(lst *l) {
	while (l != NULL && l->lstkind == WRAPPED_LIST) {
		l = l->lstdat.wrap_l.w;
	}
	return (l == NULL);
}

value hd(lst *l) {
	if (l->lstkind == WRAPPED_LIST) {
		return cast(hd(l->lstdat.wrap_l.w), l->lstdat.wrap_l.u1->tydat.tylist, l->lstdat.wrap_l.u2->tydat.tylist, l->rid, l->polarity);\
	} else {
		return l->lstdat.unwrap_l.h;
	}
}

value tl(lst *l) {
	if (l->lstkind == WRAPPED_LIST) {
		return cast(tl(l->lstdat.wrap_l.w), l->lstdat.wrap_l.u1, l->lstdat.wrap_l.u2, l->rid, l->polarity);
	} else {
		return l->lstdat.unwrap_l.t;
	}
}
#else

int is_NULL(lst *l) {
	while (l != NULL && (l->lstdat.wrap_l.c & 0b1)) {
		l = l->lstdat.wrap_l.w;
	}
	return (l == NULL);
}

value hd(lst *l) {
	if (l->lstdat.wrap_l.c & 0b1) {
		return coerce(l->lstdat.wrap_l.w->lstdat.unwrap_l.h, ((crc*)(l->lstdat.wrap_l.c & ~0b1))->crcdat.one_crc);
	} else {
		return l->lstdat.unwrap_l.h;
	}
}

value tl(lst *l) {
	if (l->lstdat.wrap_l.c & 0b1) {
		return coerce(l->lstdat.wrap_l.w->lstdat.unwrap_l.t, (crc*)(l->lstdat.wrap_l.c & ~0b1));
	} else {
		return l->lstdat.unwrap_l.t;
	}
}

#endif

#endif
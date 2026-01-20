#include <stdio.h>
#include <stdlib.h>

int did_not_match() {
	printf("didn't match");
	exit(1);
}

#if !defined(EAGER) && !defined(STATIC)
#include "lst.h"
#include "value.h"
#include "capp.h"
#include "ty.h"
#include "crc.h"

int is_NULL(lst *l) {
	while (l != NULL && l->lstkind == WRAPPED_LIST) {
		l = l->lstdat.wrap_l.w;
	}
	return (l == NULL);
}

value hd(lst *l) {
	if (l->lstkind == WRAPPED_LIST) {
		#ifdef CAST
		return cast(hd(l->lstdat.wrap_l.w), l->lstdat.wrap_l.u1->tydat.tylist, l->lstdat.wrap_l.u2->tydat.tylist, l->rid, l->polarity);
		#else
		return coerce(l->lstdat.wrap_l.w->lstdat.unwrap_l.h, l->lstdat.wrap_l.c->crcdat.one_crc);
		#endif
	} else {
		return l->lstdat.unwrap_l.h;
	}
}

value tl(lst *l) {
	if (l->lstkind == WRAPPED_LIST) {
		#ifdef CAST
		return cast(tl(l->lstdat.wrap_l.w), l->lstdat.wrap_l.u1, l->lstdat.wrap_l.u2, l->rid, l->polarity);
		#else
		return coerce(l->lstdat.wrap_l.w->lstdat.unwrap_l.t, l->lstdat.wrap_l.c);
		#endif
	} else {
		return l->lstdat.unwrap_l.t;
	}
}

#endif
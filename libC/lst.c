#include <stdio.h>
#include <stdlib.h>

int did_not_match() {
	printf("didn't match");
	exit(1);
}

#ifndef EAGER
#include "lst.h"
#include "value.h"
#include "capp.h"
#include "ty.h"
#include "crc.h"
#include "gc.h"
#include "lst.h"

int is_NULL(lst *l) {
	if (l==NULL) { 
		return 1;
	} else if (l->lstkind == WRAPPED_LIST) {
		return is_NULL(l->lstdat.wrap_l.w);
	} else {
		return 0;
	}
}

value hd(lst l) {
	if (l.lstkind == WRAPPED_LIST) {
		#ifdef CAST
		return cast(hd(*l.lstdat.wrap_l.w), l.lstdat.wrap_l.u1->tydat.tylist, l.lstdat.wrap_l.u2->tydat.tylist, l.lstdat.wrap_l.r_p);
		#else
		return coerce(*l.lstdat.wrap_l.w->lstdat.unwrap_l.h, l.lstdat.wrap_l.c->crcdat.one_crc);
		#endif
	} else {
		return *l.lstdat.unwrap_l.h;
	}
}

value tl(lst l) {
	if (l.lstkind == WRAPPED_LIST) {
		#ifdef CAST
		return cast(tl(*l.lstdat.wrap_l.w), l.lstdat.wrap_l.u1, l.lstdat.wrap_l.u2, l.lstdat.wrap_l.r_p);
		#else
		return coerce(*l.lstdat.wrap_l.w->lstdat.unwrap_l.t, l.lstdat.wrap_l.c);
		#endif
	} else {
		return *l.lstdat.unwrap_l.t;
	}
}

#endif
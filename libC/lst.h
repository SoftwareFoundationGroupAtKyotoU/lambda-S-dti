#ifndef LST_H
#define LST_H

#include "types.h"

typedef struct lst {
	#ifdef EAGER
	value *h;
	value *t;
	#else
	enum lstkind {
		UNWRAPPED_LIST,
		WRAPPED_LIST
	} lstkind;
	union lstdat {
		struct unwrap_l {
			value *h;
			value *t;
		} unwrap_l;
		struct wrap_l {
			lst *w;
			#ifdef CAST
			ty *u1;
			ty *u2;
			ran_pol r_p;
			#else
			crc *c;
			#endif
		} wrap_l;
	} lstdat;
	#endif
} lst;

int did_not_match();

#ifndef EAGER
value hd(lst*);

value tl(lst*);

int is_NULL(lst*);
#endif

#endif
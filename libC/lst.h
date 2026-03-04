#ifndef LST_H
#define LST_H

#include "types.h"

typedef struct lst {
	#if defined(EAGER) || defined(STATIC)
	value h;
	value t;
	#elif defined(CAST)
	enum lstkind : uint8_t {
		UNWRAPPED_LIST,
		WRAPPED_LIST
	} lstkind;
	uint8_t polarity;
	uint32_t rid;
	union lstdat {
		struct unwrap_l {
			value h;
			value t;
		} unwrap_l;
		struct wrap_l {
			lst *w;
			ty *u1;
			ty *u2;
		} wrap_l;
	} lstdat;
	#else
	union lstdat {
		struct unwrap_l {
			value h;
			value t;
		} unwrap_l;
		struct wrap_l {
			lst *w;
			uintptr_t c;
		} wrap_l;
	} lstdat;
	#endif
} lst;

void did_not_match() __attribute__((noreturn));

#if !defined(EAGER) && !defined(STATIC)
value hd(lst*);

value tl(lst*);

int is_NULL(lst*);
#endif

#endif
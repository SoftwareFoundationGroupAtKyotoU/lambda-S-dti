#ifndef LST_H
#define LST_H

#include "types.h"
#include "value.h"

typedef struct lst {
	#if defined(EAGER) || defined(STATIC)
	value h;
	value t;
	#else
	enum lstkind : uint8_t {
		UNWRAPPED_LIST,
		WRAPPED_LIST
	} lstkind;
	#ifdef CAST
	uint8_t polarity;
	uint32_t rid;
	#endif
	union lstdat {
		struct unwrap_l {
			value h;
			value t;
		} unwrap_l;
		struct wrap_l {
			lst *w;
			#ifdef CAST
			ty *u1;
			ty *u2;
			#else
			crc *c;
			#endif
		} wrap_l;
	} lstdat;
	#endif
} lst;

void did_not_match() __attribute__((noreturn));;

#if !defined(EAGER) && !defined(STATIC)
value hd(lst*);

value tl(lst*);

int is_NULL(lst*);
#endif

#endif
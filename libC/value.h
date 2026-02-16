#ifndef VALUE_H
#define VALUE_H

#include "types.h"

#include "dyn.h"
typedef union value {
	int64_t i_b_u;
	fun *f;
	lst *l;
	#ifndef STATIC
	dyn d;
	#ifndef CAST
	crc *s;
	#endif
	#endif
} value;

#if !defined(CAST) && !defined(STATIC)
typedef struct v_d {
	value v;
	crc *d;
} v_d;
#endif

#endif
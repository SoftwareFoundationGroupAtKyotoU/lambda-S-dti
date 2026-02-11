#ifndef VALUE_H
#define VALUE_H

#include "types.h"

typedef union value {
	int64_t i_b_u;
	#ifndef STATIC
	dyn *d;
	#endif
	fun *f;
	lst *l;
	#if !defined(CAST) && !defined(STATIC)
	crc *s;
	#endif
} value;

#endif
#ifndef VALUE_H
#define VALUE_H

#include "types.h"

typedef union value {
	int i_b_u;
	dyn *d;
	fun *f;
	lst *l;
	#ifndef CAST
	crc *s;
	#endif
} value;

#endif
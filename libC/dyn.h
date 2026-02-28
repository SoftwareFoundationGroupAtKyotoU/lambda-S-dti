#ifndef DYN_H
#define DYN_H

#ifndef STATIC

#ifdef CAST

typedef uint64_t dyn;

#else //CAST

#include "types.h"
#include "value.h"

typedef struct v_d {
	value v;
	crc *d;
} v_d;

typedef union dyn {
	uint64_t atom;
	v_d *non_atom;
} dyn;

#endif //CAST

#endif //STATIC

#endif //DYN_H
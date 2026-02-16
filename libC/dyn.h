#ifndef DYN_H
#define DYN_H

#ifndef STATIC
#include "types.h"

#ifdef CAST
typedef uint64_t dyn;
#else
typedef union dyn {
	uint64_t atom;
	v_d *non_atom;
} dyn;
#endif

#endif

#endif
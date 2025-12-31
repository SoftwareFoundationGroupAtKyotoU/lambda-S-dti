#ifndef DYN_H
#define DYN_H

#include "types.h"

typedef struct dyn {
	value *v;
	#ifdef CAST
	ground_ty g;
	ran_pol r_p;
	#else
	crc *d;
	#endif
} dyn;

#endif
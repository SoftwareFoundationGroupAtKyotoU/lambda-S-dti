#ifndef DYN_H
#define DYN_H

#include "types.h"
#include "value.h"

typedef struct dyn {
	value v;
	#ifdef CAST
	uint32_t rid;
	ground_ty g;
	uint8_t polarity;
	#else
	crc *d;
	#endif
} dyn;

#endif
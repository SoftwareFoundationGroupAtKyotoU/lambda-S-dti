#ifndef DYN_H
#define DYN_H

#ifndef STATIC

#ifdef CAST

#else //CAST

#include "types.h"

typedef struct v_d {
	value v;
	crc *d;
} v_d;

#endif //CAST

#endif //STATIC

#endif //DYN_H
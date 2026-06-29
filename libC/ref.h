#ifndef REF_H
#define REF_H

#include "types.h"

#ifdef MONOTONIC
#include "ty.h"

typedef struct ref {
	value v;
	ty *u;
} ref;
#else
typedef value *ref;
#endif

#endif
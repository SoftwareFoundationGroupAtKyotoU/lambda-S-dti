#ifndef REF_H
#define REF_H

#include "types.h"
#include "ty.h"

typedef struct ref {
	value v;
	ty *u;
} ref;

#endif
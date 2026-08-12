#ifndef DBL_H
#define DBL_H

#include "types.h"
#include <string.h>

static inline double to_double(value v) {
	double d;
	memcpy(&d, &v, sizeof(double));
	return d;
}

static inline value of_double(double d) {
	value v;
	memcpy(&v, &d, sizeof(double));
	return v;
}

#endif //DBL_H
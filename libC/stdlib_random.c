#include <stdlib.h>

#include "runtime.h"
#include "stdlib_random.h"

static inline value _core_random_init(value cls, value seed) {
	(void)cls;
	srand((unsigned int)seed);
	return 0;
}
DEF_UNARY(random_init, _core_random_init)

static inline value _core_random_int(value cls, value bound) {
	(void)cls;
	return (value)(rand() % bound);
}
DEF_UNARY(random_int, _core_random_int)

static inline value _core_random_float(value cls, value bound) {
	(void)cls;
	double ratio = (double)rand() / ((double)RAND_MAX + 1.0);
	return of_double(to_double(bound) * ratio);
}
DEF_UNARY(random_float, _core_random_float)

STDLIB_RANDOM_UNARY_LIST(STDLIB_TABLE)

STDLIB_RANDOM_UNARY_LIST(STDLIB_EXPORT)

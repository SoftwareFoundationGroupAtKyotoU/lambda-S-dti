#include "runtime.h"
#include "stdlib_basic.h"

static inline value _core_float_of_int(value cls, value x) {
	(void)cls;
	return of_double((double)x);
}
DEF_UNARY(float_of_int, _core_float_of_int)

static inline value _core_int_of_float(value cls, value x) {
	(void)cls;
	return (value)to_double(x);
}
DEF_UNARY(int_of_float, _core_int_of_float)

static inline value _core_char_of_int(value cls, value x) {
	(void)cls;
	return x;
}
DEF_UNARY(char_of_int, _core_char_of_int)

static inline value _core_int_of_char(value cls, value x) {
	(void)cls;
	return x;
}
DEF_UNARY(int_of_char, _core_int_of_char)

static inline value _core_not_ml(value cls, value b) {
	(void)cls;
	if (b == 1) {
		return 0;
	} else {
		return 1;
	}
}
DEF_UNARY(not_ml, _core_not_ml)

static inline value _core_ignore(value cls, value x) {
	(void)cls;
	(void)x;
	return 0;
}
DEF_UNARY(ignore, _core_ignore)

STDLIB_BASIC_UNARY_LIST(STDLIB_TABLE)

STDLIB_BASIC_UNARY_LIST(STDLIB_EXPORT)

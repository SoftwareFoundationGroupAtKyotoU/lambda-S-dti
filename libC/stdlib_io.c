#include "runtime.h"
#include "stdlib_io.h"

/* ---- core implementations ---- */

static inline value _core_print_int(value cls, value v) {
	(void)cls;
	printf("%ld", v);
	return 0;
}
DEF_UNARY(print_int, _core_print_int)

static inline value _core_print_bool(value cls, value v) {
	(void)cls;
	int64_t i = v;
	if (i == 1) {
		printf("true");
	} else if (i == 0) {
		printf("false");
	} else {
		printf("error:not boolean value is applied to print_bool");
		exit(1);
	}
	return 0;
}
DEF_UNARY(print_bool, _core_print_bool)

static inline value _core_print_newline(value cls, value v) {
	(void)cls;
	int64_t i = v;
	if (i == 0) {
		printf("\n");
	} else {
		printf("error:not unit value is applied to print_newline");
		exit(1);
	}
	return 0;
}
DEF_UNARY(print_newline, _core_print_newline)

static inline value _core_print_float(value cls, value v) {
	(void)cls;
	printf("%lf", to_double(v));
	return 0;
}
DEF_UNARY(print_float, _core_print_float)

static inline value _core_print_string(value cls, value v) {
	(void)cls;
	printf("%s", (char*)v);
	return 0;
}
DEF_UNARY(print_string, _core_print_string)

static inline value _core_print_char(value cls, value v) {
	(void)cls;
	putchar((int)v);
	return 0;
}
DEF_UNARY(print_char, _core_print_char)

static inline value _core_read_int(value cls, value v) {
	(void)cls;
	value retv;
	int64_t i = v;
	if (i == 0) {
		if (scanf("%ld", &retv) != 1) {
			printf("Error: Input format error or EOF.");
			exit(1);
		}
	} else {
		printf("error:not unit value is applied to read_int");
		exit(1);
	}
	return retv;
}
DEF_UNARY(read_int, _core_read_int)

static inline value _core_read_float(value cls, value v) {
	(void)cls;
	double retv;
	int64_t i = v;
	if (i == 0) {
		if (scanf("%lf", &retv) != 1) {
			printf("Error: Input format error or EOF.");
			exit(1);
		}
	} else {
		printf("error:not unit value is applied to read_float");
		exit(1);
	}
	return of_double(retv);
}
DEF_UNARY(read_float, _core_read_float)

static inline value _core_read_char(value cls, value v) {
	(void)cls;
	int64_t i = v;
	if (i != 0) {
		printf("error:not unit value is applied to read_char");
		exit(1);
	}
	int c = getchar();
	if (c == EOF) {
		printf("Error: Input format error or EOF.");
		exit(1);
	}
	return (value)c;
}
DEF_UNARY(read_char, _core_read_char)

static inline value _core_exit_ml(value cls, value v) {
	(void)cls;
	exit((int)v);
}
DEF_UNARY(exit_ml, _core_exit_ml)

STDLIB_IO_UNARY_LIST(STDLIB_TABLE)

STDLIB_IO_UNARY_LIST(STDLIB_EXPORT)

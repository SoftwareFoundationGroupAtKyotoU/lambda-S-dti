#ifndef STDLIB_MACROS_H
#define STDLIB_MACROS_H

#include "types.h"

/* function declaration (e.g. print_int) */
#ifdef ALT
// for ALT
// value fun_print_int(value, value, value);
// value fun_alt_print_int(value, value);
#define STDLIB_DECL_UNARY(n) \
  value fun_##n(value, value, value); \
  value fun_alt_##n(value, value);
#elif defined(CAST) || defined(STATIC)
// for CAST or STATIC
// value fun_print_int(value, value);
#define STDLIB_DECL_UNARY(n) \
  value fun_##n(value, value);
#else
// otherwise
// value fun_print_int(value, value, value);
#define STDLIB_DECL_UNARY(n) \
  value fun_##n(value, value, value);
#endif

// for binary function, preparing one more function applied only one argument (e.g. min)
// value fun_min(value, value, value);
// value fun_min_x(value, value, value);
#define STDLIB_DECL_BINARY(n) \
  STDLIB_DECL_UNARY(n) \
  STDLIB_DECL_UNARY(n##_x)

/* extern values (e.g. print_int) */
// extern value print_int;
#define STDLIB_DECL_EXTERN(n) extern value n;

/* ---- codegen macros used inside each category .c file ---- */

#ifdef ALT
#define DEF_UNARY(fname, core) \
  value fun_##fname(value cls, value v, value w) { return apply_coerce(core(cls, v), (crc*)w); } \
  value fun_alt_##fname(value cls, value v) { return core(cls, v); }
#define DEF_BINARY(fname) \
  value fun_alt_##fname(value cls, value x) { \
    value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1); \
    ((fun*)retv)->funcM = fun_alt_##fname##_x; \
    ((fun*)retv)->funcD = fun_##fname##_x; \
    ((fun*)retv)->env[0] = (void*)x; \
    return retv; \
  } \
  value fun_##fname(value cls, value x, value w) { \
    value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1); \
    ((fun*)retv)->funcM = fun_alt_##fname##_x; \
    ((fun*)retv)->funcD = fun_##fname##_x; \
    ((fun*)retv)->env[0] = (void*)x; \
    return apply_coerce(retv, (crc*)w); \
  }
#elif defined(CAST) || defined(STATIC)
#define DEF_UNARY(fname, core) \
  value fun_##fname(value cls, value v) { return core(cls, v); }
#define DEF_BINARY(fname) \
  value fun_##fname(value cls, value x) { \
    value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1); \
    ((fun*)retv)->funcM = fun_##fname##_x; \
    ((fun*)retv)->env[0] = (void*)x; \
    return retv; \
  }
#else
#define DEF_UNARY(fname, core) \
  value fun_##fname(value cls, value v, value w) { return apply_coerce(core(cls, v), (crc*)w); }
#define DEF_BINARY(fname) \
  value fun_##fname(value cls, value x, value w) { \
    value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1); \
    ((fun*)retv)->funcD = fun_##fname##_x; \
    ((fun*)retv)->env[0] = (void*)x; \
    return apply_coerce(retv, (crc*)w); \
  }
#endif

#ifdef ALT
#define STDLIB_TABLE(n) static fun f_##n = { .funcD = fun_##n, .funcM = fun_alt_##n };
#elif defined(CAST) || defined(STATIC)
#define STDLIB_TABLE(n) static fun f_##n = { .funcM = fun_##n };
#else
#define STDLIB_TABLE(n) static fun f_##n = { .funcD = fun_##n };
#endif

#define STDLIB_EXPORT(n) value n = (value)&f_##n;

#endif // STDLIB_MACROS_H

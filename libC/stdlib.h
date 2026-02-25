#ifndef STDLIB_H
#define STDLIB_H

#include "types.h"

#ifdef ALT
value fun_print_int(value, value, value);
value fun_print_bool(value, value, value);
value fun_print_newline(value, value, value);
value fun_read_int(value, value, value);
value fun_ignore(value, value, value);
value fun_abs_ml(value, value, value);
value fun_max(value, value, value);
value fun_max_x(value, value, value);
value fun_min(value, value, value);
value fun_min_x(value, value, value);
value fun_prec(value, value, value);
value fun_succ(value, value, value);
value fun_not_ml(value, value, value);

value fun_alt_print_int(value, value);
value fun_alt_print_bool(value, value);
value fun_alt_print_newline(value, value);
value fun_alt_read_int(value, value);
value fun_alt_ignore(value, value);
value fun_alt_abs_ml(value, value);
value fun_alt_max(value, value);
value fun_alt_min(value, value);
value fun_alt_prec(value, value);
value fun_alt_succ(value, value);
value fun_alt_not_ml(value, value);
#elif defined(CAST) || defined(STATIC)
value fun_print_int(value, value);
value fun_print_bool(value, value);
value fun_print_newline(value, value);
value fun_read_int(value, value);
value fun_ignore(value, value);
value fun_abs_ml(value, value);
value fun_max(value, value);
value fun_max_x(value, value);
value fun_min(value, value);
value fun_min_x(value, value);
value fun_prec(value, value);
value fun_succ(value, value);
value fun_not_ml(value, value);
#else
value fun_print_int(value, value, value);
value fun_print_bool(value, value, value);
value fun_print_newline(value, value, value);
value fun_read_int(value, value, value);
value fun_ignore(value, value, value);
value fun_abs_ml(value, value, value);
value fun_max(value, value, value);
value fun_max_x(value, value, value);
value fun_min(value, value, value);
value fun_min_x(value, value, value);
value fun_prec(value, value, value);
value fun_succ(value, value, value);
value fun_not_ml(value, value, value);
#endif

extern value max_int;
extern value min_int;
extern value print_int;
extern value print_bool;
extern value print_newline;
extern value read_int;
extern value ignore;
extern value abs_ml;
extern value max;
extern value min;
extern value prec;
extern value succ;
extern value not_ml;

#endif
#ifndef STDLIB_H
#define STDLIB_H

#include "types.h"

#ifdef ALT
value fun_print_int(value, value);
value fun_print_bool(value, value);
value fun_print_newline(value, value);
value fun_read_int(value, value);
value fun_ignore(value, value, ty**);
value fun_abs_ml(value, value);
value fun_max(value, value);
value fun_max_x(value, value, value*);
value fun_min(value, value);
value fun_min_x(value, value, value*);
value fun_prec(value, value);
value fun_succ(value, value);
value fun_not_ml(value, value);

value fun_alt_print_int(value);
value fun_alt_print_bool(value);
value fun_alt_print_newline(value);
value fun_alt_read_int(value);
value fun_alt_ignore(value, ty**);
value fun_alt_abs_ml(value);
value fun_alt_max(value);
value fun_alt_max_x(value, value*);
value fun_alt_min(value);
value fun_alt_min_x(value, value*);
value fun_alt_prec(value);
value fun_alt_succ(value);
value fun_alt_not_ml(value);
#elif defined(CAST) || defined(STATIC)
value fun_print_int(value);
value fun_print_bool(value);
value fun_print_newline(value);
value fun_read_int(value);
#ifdef STATIC
value fun_ignore(value);
#else
value fun_ignore(value, ty**);
#endif
value fun_abs_ml(value);
value fun_max(value);
value fun_max_x(value, value*);
value fun_min(value);
value fun_min_x(value, value*);
value fun_prec(value);
value fun_succ(value);
value fun_not_ml(value);
#else
value fun_print_int(value, value);
value fun_print_bool(value, value);
value fun_print_newline(value, value);
value fun_read_int(value, value);
value fun_ignore(value, value, ty**);
value fun_abs_ml(value, value);
value fun_max(value, value);
value fun_max_x(value, value, value*);
value fun_min(value, value);
value fun_min_x(value, value, value*);
value fun_prec(value, value);
value fun_succ(value, value);
value fun_not_ml(value, value);
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
#ifndef STDLIB_H
#define STDLIB_H

#include "coerce.h"

extern value fun_print_int(value, value);
extern value fun_print_bool(value, value);
extern value fun_print_newline(value, value);
extern value fun_ignore(value, value, ty**);
extern value fun_abs_ml(value, value);
extern value fun_max(value, value);
extern value fun_max_x(value, value, value*);
extern value fun_min(value, value);
extern value fun_min_x(value, value, value*);
extern value fun_prec(value, value);
extern value fun_succ(value, value);
extern value fun_not(value, value);

extern value max_int;
extern value min_int;
extern value print_int;
extern value print_bool;
extern value print_newline;
extern value ignore;
extern value abs_ml;
extern value max;
extern value min;
extern value prec;
extern value succ;
extern value not;

extern int stdlibS();

#endif 
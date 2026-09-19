#ifndef STDLIB_IO_H
#define STDLIB_IO_H

#include "types.h"
#include "stdlib_macros.h"

#define STDLIB_IO_UNARY_LIST(X) \
  X(print_int) X(print_bool) X(print_newline) X(print_float) X(print_string) X(print_char) \
  X(read_int) X(read_float) X(read_char) X(exit_ml)

STDLIB_IO_UNARY_LIST(STDLIB_DECL_UNARY)

STDLIB_IO_UNARY_LIST(STDLIB_DECL_EXTERN)

#endif

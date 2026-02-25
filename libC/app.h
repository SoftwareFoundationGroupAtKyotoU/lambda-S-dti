#ifndef APP_H
#define APP_H

#ifndef STATIC
#include "types.h"

#if defined(CAST) || defined(ALT)
value fun_wrapped_call_funcM(value, value);
#endif // CAST || ALT

#ifndef CAST
value fun_wrapped_call_funcD(value, value, value);
#endif // not CAST

#endif // not STATIC

#endif // APP_H
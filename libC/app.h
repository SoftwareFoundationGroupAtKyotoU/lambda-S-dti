#ifndef APP_H
#define APP_H

#include "types.h"

#if defined(CAST) || defined(ALT) || defined(STATIC)
value appM(value, value);
#endif

#if !defined(CAST) && !defined(STATIC)
value appD(value, value, value);
#endif

#endif
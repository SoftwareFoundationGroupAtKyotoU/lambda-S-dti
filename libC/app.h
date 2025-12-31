#ifndef APP_H
#define APP_H

#include "types.h"

#if defined(CAST) || defined(ALT)
value appM(value, value);
#endif

#ifndef CAST
value appD(value, value, value);
#endif

#endif
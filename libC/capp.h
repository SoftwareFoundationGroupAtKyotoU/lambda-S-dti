#ifndef CAPP_H
#define CAPP_H

#include "types.h"

#ifdef CAST
value cast(value, ty*, ty*, ran_pol);
#else
value coerce(value, crc*);
#endif

int blame(ran_pol);

#endif
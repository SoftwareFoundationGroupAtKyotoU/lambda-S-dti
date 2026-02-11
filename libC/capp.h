#ifndef CAPP_H
#define CAPP_H

#ifndef STATIC
#include "types.h"

#ifdef CAST
value cast(value, ty*, ty*, uint32_t, uint8_t);
#else
value coerce(value, crc*);
#endif

int blame(uint32_t, uint8_t);
#endif

#endif
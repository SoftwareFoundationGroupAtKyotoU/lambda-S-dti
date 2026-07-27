#ifndef CAPP_H
#define CAPP_H

#ifndef STATIC
#include "types.h"

#ifdef CAST
value cast(value, ty*, ty*, uint32_t, uint8_t);
#else

#ifdef MONOTONIC

typedef enum valkind {
	PSI_REF,
	PSI_ARRAY,
} valkind;

typedef struct {
	value r;
	valkind k;
	ty *u;
} ValueTyPair;

typedef struct {
	ValueTyPair* data;
	uint64_t count;
	uint64_t capacity;
} SuspendedCasts;

extern SuspendedCasts psi;

void sc_init(uint64_t initial_capacity);
void sc_push(value r, valkind k, ty *u);
void consume(void);
#endif

value coerce(value, crc*);

static inline value toplevel_coerce(value v, crc* s) {
	#ifdef MONOTONIC
	value v_ = coerce(v, s);
	consume();
	return v_;
	#else
	return coerce(v, s);
	#endif
}

#endif

#endif
#endif
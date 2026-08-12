#ifndef CAPP_H
#define CAPP_H

#ifndef STATIC
#include "types.h"
#include "blame.h"
#include "tpl.h"
#include <gc.h>

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

#endif

#ifdef PROFILE
static inline void update_longest(int new) {
	if (new > current_longest) current_longest = new;
	return;
}
#endif

static inline uint8_t tag_of(value v) {
	uint8_t tag = v & 0b111;
	switch (tag) {
		case G_BOOL: {
			if (v == (0b10000 | G_BOOL)) return G_UNIT;
			return G_BOOL;
		}
		default: return tag;
	}
}

static inline value tag_value(value v, ground_ty t) {
	#ifdef PROFILE
	update_longest(1);
	#endif
	switch (t) {
		case G_FN:
		case G_LI:
		case G_TP:
		case G_RF:
		case G_AR:
			return (value)(v | t);
		case G_INT:
		case G_BOOL:
			return (value)(v << 3 | t);
		case G_FLOAT: {
			value *v_ = GC_MALLOC(sizeof(value*));
			*v_ = v;
			return (value)((value)v_ | t);
		}
		case G_UNIT:
			return (value)(0b10000 | G_BOOL);
	}
}

static inline value untag_value(value v, ground_ty t) {
	switch (t) {
		case G_INT:
		case G_BOOL:
			return (value)(v >> 3);
		case G_UNIT:
			return 0b0;
		case G_FLOAT:
			return *(value*)(v & ~0b111);
		case G_FN:
		case G_LI:
		case G_TP:
		case G_RF:
		case G_AR:
			return (value)(v & ~0b111);
	}
}

static inline uint16_t size_of(value v) {
	switch (tag_of(v)) {
		case G_TP: {
			#ifdef EAGER
			return ((tpl*)untag_value(v, G_TP))->hdr.size;
			#else
			return ((tpl*)untag_value(v, G_TP))->size;
			#endif
		}
		default: return 0;
	}
}

#ifndef CAST

static inline value toplevel_coerce(value v, crc* s) {
	#ifdef MONOTONIC
	value v_ = coerce(v, s);
	consume();
	return v_;
	#else
	return coerce(v, s);
	#endif
}

static inline value toplevel_coerce_inj(value v, ground_ty g) {
	#ifdef PROFILE
	current_cast++;
	#endif
	return tag_value(v, g);
}

static inline value toplevel_coerce_proj(value v, ground_ty g, uint32_t rid, uint8_t polarity) {
	#ifdef PROFILE
	current_cast++;
	#endif
	if (tag_of(v) != g) { blame(rid, polarity); }
	return untag_value(v, g);
}

static inline value toplevel_coerce_proj_tp(value v, uint16_t size, uint32_t rid, uint8_t polarity) {
	#ifdef PROFILE
	current_cast++;
	#endif
	if (tag_of(v) != G_TP || size_of(v) != size) { blame(rid, polarity); }
	return untag_value(v, G_TP);
}

#endif

#endif
#endif
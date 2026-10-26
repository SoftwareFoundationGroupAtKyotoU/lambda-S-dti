#ifndef CAPP_H
#define CAPP_H

#ifndef STATIC
#include "types.h"
#include "blame.h"
#include "tpl.h"
#include <stdio.h>
#include <stdlib.h>
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

value coerce(value, crc*, uint8_t);

#endif

#ifdef PROFILE
static inline void update_longest(int new) {
	if (new > current_longest) current_longest = new;
	return;
}
#endif

typedef enum ptag : uint8_t {
	PTAG_FN,
	PTAG_LI,
	PTAG_TP,
	PTAG_RF,
	PTAG_AR,
	PTAG_INT,
	PTAG_BOOL_UNIT_CHAR,
	// PTAG_BOOL_UNIT_CHAR is shared by G_BOOL, G_UNIT, and G_CHAR:
	// a plain bool is `v << 3 | tag` for v in {0,1};
	// bit 4 set means "not a plain bool", and among those, 
	// bit 3 clear is G_UNIT (`0b10000 | tag`), and
	// bit 3 set is G_CHAR (`v << 5 | 0b11000 | tag`) --
	// see tag_of/tag_value/untag_value below.
	PTAG_BOXED,
	// PTAG_BOXED is shared by float, string.
} ptag;

static inline ptag ptag_of_ground_ty(ground_ty g) {
	switch (g) {
		case G_FN: return PTAG_FN;
		case G_LI: return PTAG_LI;
		case G_TP: return PTAG_TP;
		case G_RF: return PTAG_RF;
		case G_AR: return PTAG_AR;
		case G_INT: return PTAG_INT;
		case G_BOOL:
		case G_UNIT:
		case G_CHAR: return PTAG_BOOL_UNIT_CHAR;
		case G_FLOAT:
		case G_STRING: return PTAG_BOXED;
	}
}

static inline ground_ty ground_ty_of_tag(ptag tag) {
	switch (tag) {
		case PTAG_FN: return G_FN;
		case PTAG_LI: return G_LI;
		case PTAG_TP: return G_TP;
		case PTAG_RF: return G_RF;
		case PTAG_AR: return G_AR;
		case PTAG_INT: return G_INT;
		case PTAG_BOOL_UNIT_CHAR:
		case PTAG_BOXED:
			// omit ambiguous part
			fprintf(stderr, "ground_ty_of_tag: ambiguous ptag %d\n", tag);
			exit(1);
	}
}

typedef enum boxed_kind : uint8_t {
	BOX_FLOAT,
	BOX_STRING,
} boxed_kind;

typedef struct boxed {
	uint8_t kind;
	value v;
} boxed;

static inline uint8_t tag_of(value v) {
	ptag tag = v & 0b111;
	switch (tag) {
		case PTAG_BOOL_UNIT_CHAR: {
			if (v & 0b10000) {
				if (v & 0b01000) return G_CHAR;
				return G_UNIT;
			}
			return G_BOOL;
		}
		case PTAG_BOXED: {
			boxed *b = (boxed*)(v & ~0b111);
			switch (b->kind) {
				case BOX_FLOAT: return G_FLOAT;
				case BOX_STRING: return G_STRING;
			}
		}
		default: return ground_ty_of_tag(tag);
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
			return (value)(v | ptag_of_ground_ty(t));
		case G_INT:
		case G_BOOL:
			return (value)(v << 3 | ptag_of_ground_ty(t));
		case G_FLOAT: {
			boxed *b = GC_MALLOC(sizeof(boxed));
			b->kind = BOX_FLOAT;
			b->v = v;
			return (value)((value)b | PTAG_BOXED);
		}
		case G_STRING: {
			boxed *b = GC_MALLOC(sizeof(boxed));
			b->kind = BOX_STRING;
			b->v = v;
			return (value)((value)b | PTAG_BOXED);
		}
		case G_UNIT:
			return (value)(0b10000 | PTAG_BOOL_UNIT_CHAR);
		case G_CHAR:
			return (value)((v << 5) | 0b11000 | PTAG_BOOL_UNIT_CHAR);
	}
}

static inline value untag_value(value v, ground_ty t) {
	switch (t) {
		case G_INT:
		case G_BOOL:
			return (value)(v >> 3);
		case G_UNIT:
			return 0b0;
		case G_CHAR:
			return (value)(v >> 5);
		case G_FLOAT:
		case G_STRING: {
			boxed *b = (boxed*)(v & ~0b111);
			return b->v;
		}
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
#include "crc.h"

static inline value apply_coerce(value v, crc* s) {
	return coerce(v, s, 0);
}

static inline value apply_coerce_inj(value v, ground_ty g) {
	#ifdef PROFILE
	current_cast++;
	coerce_kind[C_ID]++;
	#endif
	return tag_value(v, g);
}

static inline value apply_coerce_proj(value v, ground_ty g, uint32_t rid, uint8_t polarity) {
	#ifdef PROFILE
	current_cast++;
	coerce_kind[C_ID]++;
	#endif
	if (tag_of(v) != g) { blame(rid, polarity); }
	return untag_value(v, g);
}

static inline value apply_coerce_proj_tp(value v, uint16_t size, uint32_t rid, uint8_t polarity) {
	#ifdef PROFILE
	current_cast++;
	coerce_kind[C_ID]++;
	#endif
	if (tag_of(v) != G_TP || size_of(v) != size) { blame(rid, polarity); }
	return untag_value(v, G_TP);
}

#ifdef MONOTONIC
#include "ty.h"

// Read the element of monotonic ref/array which RTTI is U as Dyn value.
// Same as apply_coerce(v, make_s_coercion_to_dyn(u)), but short-circuit.
static inline value read_to_dyn(value v, ty *u) {
	switch (u->tykind) {
		case DYN: {
			#ifdef PROFILE
			current_cast++;
			coerce_kind[C_ID]++;
			#endif
			return v;
		}
		case BASE_INT: return apply_coerce_inj(v, G_INT);
		case BASE_BOOL: return apply_coerce_inj(v, G_BOOL);
		case BASE_UNIT: return apply_coerce_inj(v, G_UNIT);
		case BASE_FLOAT: return apply_coerce_inj(v, G_FLOAT);
		case BASE_CHAR: return apply_coerce_inj(v, G_CHAR);
		case BASE_STRING: return apply_coerce_inj(v, G_STRING);
		default: return coerce(v, make_s_coercion_to_dyn(u), 0);
	}
}

// write the dyn value to monotonic ref/array which has u as RTTI
// Same as coerce(v, make_s_coercion_from_dyn(u), 1), but short-circuit.
static inline value write_from_dyn(value v, ty *u) {
	switch (u->tykind) {
		case DYN: {
			#ifdef PROFILE
			current_cast++;
			coerce_kind[C_ID]++;
			#endif
			return v;
		}
		case BASE_INT: return apply_coerce_proj(v, G_INT, 0, 0);
		case BASE_BOOL: return apply_coerce_proj(v, G_BOOL, 0, 0);
		case BASE_UNIT: return apply_coerce_proj(v, G_UNIT, 0, 0);
		case BASE_FLOAT: return apply_coerce_proj(v, G_FLOAT, 0, 0);
		case BASE_CHAR: return apply_coerce_proj(v, G_CHAR, 0, 0);
		case BASE_STRING: return apply_coerce_proj(v, G_STRING, 0, 0);
		default: return coerce(v, make_s_coercion_from_dyn(u), 1);
	}
}

// skip comsume if psi is empty
static inline void consume_pending(void) {
	if (psi.count) consume();
}
#endif

#endif

#endif
#endif
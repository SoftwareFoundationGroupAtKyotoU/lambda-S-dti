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

value coerce(value, crc*, uint8_t);

#endif

#ifdef PROFILE
static inline void update_longest(int new) {
	if (new > current_longest) current_longest = new;
	return;
}
#endif

// Physical 3-bit tag embedded in the low bits of a `value` -- strictly the 8 patterns 000-111.
// Kept as its own type, distinct from `ground_ty` (the logical dynamic type), because one
// physical code -- PTAG_BOXED -- is shared by every ground type whose payload doesn't fit
// inline (see `boxed` below), and PTAG_BOOL_UNIT is likewise shared by G_BOOL and G_UNIT.
// Order must match `ground_ty` (types.h)'s first 8 members; converted via
// ptag_of_ground_ty/ground_ty_of_tag below rather than relied on implicitly.
typedef enum ptag : uint8_t {
	PTAG_FN,
	PTAG_LI,
	PTAG_TP,
	PTAG_RF,
	PTAG_AR,
	PTAG_INT,
	PTAG_BOOL_UNIT,
	PTAG_BOXED,
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
		case G_UNIT: return PTAG_BOOL_UNIT;
		case G_FLOAT: return PTAG_BOXED;
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
		case PTAG_BOOL_UNIT: return G_BOOL; // ambiguous with G_UNIT; tag_of disambiguates before falling here
		case PTAG_BOXED: return G_FLOAT;    // ambiguous with other boxed kinds; tag_of disambiguates before falling here
	}
}

// Generic box for ground types whose payload doesn't fit inline in a tagged `value` (see
// docs/todo.md "「Boxed」的な汎用タグの導入"). `kind` disambiguates which ground type a given
// box actually holds. Only BOX_FLOAT exists today (this is a pure refactor of the existing
// float-boxing code, kept behavior-identical) -- a future type (e.g. a string) would add its
// own `boxed_kind` plus one `case` in each of tag_of/tag_value/untag_value below, spending no
// new physical tag.
typedef enum boxed_kind : uint8_t {
	BOX_FLOAT,
} boxed_kind;

typedef struct boxed {
	uint8_t kind;
	value v;
} boxed;

static inline uint8_t tag_of(value v) {
	ptag tag = v & 0b111;
	switch (tag) {
		case PTAG_BOOL_UNIT: {
			if (v == (0b10000 | PTAG_BOOL_UNIT)) return G_UNIT;
			return G_BOOL;
		}
		case PTAG_BOXED: {
			boxed *b = (boxed*)(v & ~0b111);
			switch (b->kind) {
				case BOX_FLOAT: return G_FLOAT;
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
		case G_UNIT:
			return (value)(0b10000 | PTAG_BOOL_UNIT);
	}
}

static inline value untag_value(value v, ground_ty t) {
	switch (t) {
		case G_INT:
		case G_BOOL:
			return (value)(v >> 3);
		case G_UNIT:
			return 0b0;
		case G_FLOAT: {
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

static inline value apply_coerce(value v, crc* s) {
	return coerce(v, s, 0);
}

static inline value apply_coerce_inj(value v, ground_ty g) {
	#ifdef PROFILE
	current_cast++;
	#endif
	return tag_value(v, g);
}

static inline value apply_coerce_proj(value v, ground_ty g, uint32_t rid, uint8_t polarity) {
	#ifdef PROFILE
	current_cast++;
	blame_check_num++;
	#endif
	if (tag_of(v) != g) { blame(rid, polarity); }
	return untag_value(v, g);
}

static inline value apply_coerce_proj_tp(value v, uint16_t size, uint32_t rid, uint8_t polarity) {
	#ifdef PROFILE
	current_cast++;
	blame_check_num++;
	#endif
	if (tag_of(v) != G_TP || size_of(v) != size) { blame(rid, polarity); }
	return untag_value(v, G_TP);
}

#endif

#endif
#endif
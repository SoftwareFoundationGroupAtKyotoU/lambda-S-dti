#ifndef CRC_H
#define CRC_H

#if !defined(CAST) && !defined(STATIC)
#include <stdint.h>
#include "types.h"

typedef struct crc {
	enum crckind : uint8_t {
		C_ID,
		C_FUN,
		C_LIST,
		C_TUPLE,
		C_REF,
		C_ARRAY,
		C_TV,
		C_BOT
	} crckind;

	uint8_t has_proj : 1;
	uint8_t has_inj : 1;

	uint8_t has_tv  : 1;

	uint8_t p_proj : 1;
	uint32_t rid_proj;

	// payload: 16byte
	union crcdat {
		struct {
			ground_ty g; // for ID
			uint16_t size;
		} id;
		struct fun_crc { // for FUN
			crc *c1;
			crc *c2;
		} fun_crc;
		crc *lst_crc; // for LIST
		struct tpl_crc { // for TUPLE
			uint16_t size;
			crc **crcs;
		} tpl_crc;
		#ifdef MONOTONIC
		ty *mref_crc; // for MREF
		ty *marray_crc; // for MARRAY
		#else
		struct ref_crc { // for REF
			crc *c1;
			crc *c2;
		} ref_crc;
		struct array_crc { // for ARRAY
			crc *c1;
			crc *c2;
		} array_crc;
		#endif
		struct tv {
			uint32_t rid_inj;
			uint8_t p_inj : 1;
			ty *tv_ptr;
		} tv;
		struct bot { // for BOT
			ground_ty g;
			uint16_t size;
			uint32_t rid_bot;
		    uint8_t p_bot : 1;
			uint8_t kind_bot : 1; // 0 for BOT, 1 for OCCUR
		} bot;
	} crcdat;
} crc;

// NOTE: rewrite if you change the definition of crckind
#define N_CRCKIND (C_BOT + 1)

crc *compose(crc*, crc*);

crc *normalize_tv(crc*);
crc *normalize_bot_tv(crc*);

// void trace_crc(const char*, crc*);

extern crc crc_id;
extern crc crc_inj_INT;
extern crc crc_inj_BOOL;
extern crc crc_inj_UNIT;
extern crc crc_inj_FLOAT;
extern crc crc_inj_FN;
extern crc crc_inj_LI;
extern crc crc_inj_RF;
extern crc crc_inj_AR;

crc* alloc_crc(crc*);

#ifdef HASH
void set_static_crcs(crc**, int);
void clear_crc_caches();
#endif //HASH

#ifdef MONOTONIC
crc *make_s_coercion(ty*, ty*);

// 複合型(TyFun/TyList/TyTuple)の外殻組み立てヘルパー。toC.ml がタグ判定+中身の再帰を行った後に呼ぶ。
crc *wrap_list(crc*);
crc *wrap_tuple(uint16_t, crc**);
crc *wrap_fn(crc*, crc*);

crc *make_s_coercion_to_dyn(ty*);
crc *make_s_coercion_to_ground(ty*, ground_ty);
crc *make_s_coercion_to_mref(ty*, ty*);
crc *make_s_coercion_to_marray(ty*, ty*);

crc *make_s_coercion_from_dyn(ty*);
crc *make_s_coercion_from_ground(ground_ty, ty*);
crc *make_s_coercion_from_mref(ty*);
crc *make_s_coercion_from_marray(ty*);
#endif

#endif
#endif
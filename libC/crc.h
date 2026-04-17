#ifndef CRC_H
#define CRC_H

#if !defined(CAST) && !defined(STATIC)
#include <stdint.h>
#include "types.h"

// TODO: ground_tyにNONE,TVを追加し，SEQ_やTV_を消す最適化(?)が考えられる
  // -> プログラムは読みやすくなるが，計算時間は速くはならなさそう
typedef struct crc {
	// header: 6byte
	enum crckind : uint8_t {
		ID, // 0
		BOT, // 1
		SEQ_INJ, //2
		SEQ_PROJ, //3
		SEQ_PROJ_INJ, //4
		SEQ_PROJ_BOT, //5
		TV_INJ, //6
		TV_PROJ, //7
		TV_PROJ_INJ, //8
		TV_PROJ_OCCUR, //9
		FUN, //10
		LIST, //11
		TUPLE, //12
	} crckind;
	uint8_t p_proj  : 1;
    uint8_t p_inj   : 1;
    uint8_t botkind : 1; // 0 for BOT, 1 for OCCUR
    uint8_t has_tv  : 1;
	
	ground_ty g_proj;
	ground_ty g_inj;
	uint16_t arity_proj;
	uint16_t arity_inj;

	// payload: 16byte
	union crcdat {
		struct seq_tv { // for SEQ_, TV_, BOT
			uint32_t rid_proj;
			uint32_t rid_inj;
			union ptr {
				crc *s; // for SEQ_
				ty *tv; // for TV_
			} ptr;
		} seq_tv;
		struct fun_crc { // for FUN
			crc *c1;
			crc *c2;
		} fun_crc;
		crc *lst_crc; // for LIST
		struct tpl_crc { // for TUPLE
			uint16_t arity;
			crc **crcs;
		} tpl_crc;
	} crcdat;
} crc;

void dti(const ground_ty g, const uint16_t arity, ty *tv);

crc *compose(crc*, crc*);
crc *compose_funs(crc*, crc*);
crc *compose_lists(crc*, crc*);
crc *compose_tuples(crc*, crc*);

crc *normalize_tv_inj(crc*);
crc *normalize_tv_proj(crc*);
crc *normalize_tv_proj_inj(crc*);
crc *normalize_tv_proj_occur(crc*);

extern crc crc_id;
extern crc crc_inj_INT;
extern crc crc_inj_BOOL;
extern crc crc_inj_UNIT;
extern crc crc_inj_AR;
extern crc crc_inj_LI;

crc* alloc_crc(crc*);

#ifdef HASH
void register_static_crc(crc*);
void clear_crc_caches();
#endif //HASH

#endif

#endif
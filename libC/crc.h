#ifndef CRC_H
#define CRC_H

#if !defined(CAST) && !defined(STATIC)
#include <stdint.h>
#include "types.h"

// TODO: ground_tyにNONE,TVを追加し，SEQ_やTV_を消す最適化(?)が考えられる
  // -> プログラムは読みやすくなるが，計算時間は速くはならなさそう
typedef struct crc {
	// header: 4byte
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
	} crckind;
	ground_ty g_proj;
	ground_ty g_inj;
	uint8_t p_proj;
	uint8_t p_inj;
	uint8_t botkind; // 0 for BOT, 1 for OCCUR
	// padding: 2byte

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
		struct two_crc { // for FUN
			crc *c1;
			crc *c2;
		} two_crc;
		crc *one_crc; // for LIST
	} crcdat;
} crc;

crc *compose(crc*, crc*);

void normalize_crc(crc*);

extern crc crc_id;
extern crc crc_inj_INT;
extern crc crc_inj_BOOL;
extern crc crc_inj_UNIT;

#endif

#endif
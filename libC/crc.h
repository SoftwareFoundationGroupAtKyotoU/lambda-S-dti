#ifndef CRC_H
#define CRC_H

#if !defined(CAST) && !defined(STATIC)
#include <stdint.h>
#include "types.h"

typedef struct crc {
	// header: 4byte
	enum crckind : uint8_t {
		ID, // 0
		BOT, // 1
		// OCCUR, //2
		SEQ_INJ, //3
		SEQ_PROJ, //4
		SEQ_PROJ_INJ, //5
		SEQ_PROJ_BOT, //6
		TV_INJ, //7
		TV_PROJ, //8
		TV_PROJ_INJ, //9
		// TV_PROJ_OCCUR, //10
		FUN, //11
		LIST, //12
	} crckind;
	ground_ty g_proj;
	ground_ty g_inj;
	uint8_t p_proj;
	uint8_t p_inj;
	// padding: 3byte

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
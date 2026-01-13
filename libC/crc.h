#ifndef CRC_H
#define CRC_H

#ifndef CAST
#include <stdint.h>
#include "types.h"

typedef struct crc {
	// header: 4byte
	enum crckind : uint8_t {
		ID, // 0
		BOT, // 1
		SEQ_INJ, //2
		SEQ_PROJ, //3
		SEQ_PROJ_INJ, //4
		TV_INJ, //5
		TV_PROJ, //6
		TV_PROJ_INJ, //7
		FUN, //8
		LIST, //9
	} crckind;
	ground_ty g_inj;
	ground_ty g_proj;
	uint8_t polarity;
	// (padding: 4byte)

	// payload: 16byte
	union crcdat {
		uint32_t rid; // for BOT
		struct seq_tv { // for SEQ_, TV_
			uint32_t rid;
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

crc *normalize_crc(crc*);

extern crc crc_id;
extern crc crc_inj_INT;
extern crc crc_inj_BOOL;
extern crc crc_inj_UNIT;

#endif

#endif
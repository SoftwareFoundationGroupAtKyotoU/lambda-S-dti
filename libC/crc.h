#ifndef CRC_H
#define CRC_H

#ifndef CAST
#include "types.h"

typedef struct crc {
	enum crckind {
		INJ, //0
		PROJ, //1
		INJ_TV, //2
		PROJ_TV, //3
		PROJ_INJ_TV, //4
		FUN, //5
		LIST, //6
		ID, //7
		SEQ, //8
		BOT //9
	} crckind;
	union crcdat {
		ground_ty g;
		ty *tv;
		struct two_crc {
			crc *c1;
			crc *c2;
		} two_crc;
		crc *one_crc;
	} crcdat;
	ran_pol r_p;
} crc;

crc *compose(crc*, crc*);

crc *normalize_crc(crc*);

extern crc crc_id;
extern crc crc_inj_INT;
extern crc crc_inj_BOOL;
extern crc crc_inj_UNIT;
extern crc inj_AR;
extern crc inj_LI;
extern value crc_id_value;

crc *make_crc_inj_ar(crc*);
crc *make_crc_inj_li(crc*);
crc *make_crc_proj(ground_ty, ran_pol, crc*);
crc *make_crc_fun(crc*, crc*);
crc *make_crc_list(crc*);
#endif

#endif
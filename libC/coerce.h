#ifndef COERCE_H
#define COERCE_H

typedef struct ran_pol {
	char *filename;
	int startline;
	int startchr;
	int endline;
	int endchr;
	int polarity;
} ran_pol;

typedef enum ground_ty {
	G_INT,
	G_BOOL,
	G_UNIT,
	G_AR,
	G_LI,
} ground_ty;

typedef struct ty ty;

typedef struct ty {
	enum tykind {
		DYN,
		BASE_INT,
		BASE_BOOL,
		BASE_UNIT,
		TYFUN,
		TYLIST,
		TYVAR,
		SUBSTITUTED,
	} tykind;
	union tydat {
		ty *tv;
		struct tyfun {
			ty *left;
			ty *right;
		} tyfun;
		ty *tylist;
	} tydat;
} ty;

typedef struct crc crc;

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

int did_not_match();

int blame(ran_pol);

crc *normalize_crc(crc*);

extern ty tydyn;
extern ty tyint;
extern ty tybool;
extern ty tyunit;
extern ty tyar;
extern ty tyli;
extern ty *(newty)();

extern crc crc_id;
extern crc crc_inj_INT;
extern crc crc_inj_BOOL;
extern crc crc_inj_UNIT;
extern crc inj_AR;
extern crc inj_LI;

crc *make_crc_inj_ar(crc*);
crc *make_crc_inj_li(crc*);
crc *make_crc_proj(ground_ty, ran_pol, crc*);
crc *make_crc_fun(crc*, crc*);
crc *make_crc_list(crc*);

#endif
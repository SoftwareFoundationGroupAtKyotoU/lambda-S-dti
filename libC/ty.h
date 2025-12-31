#ifndef TY_H
#define TY_H

#include "types.h"

typedef struct ty {
	enum tykind {
		DYN, //0
		BASE_INT, //1
		BASE_BOOL, //2
		BASE_UNIT, //3
		TYFUN, //4
		TYLIST, //5
		TYVAR, //6
		#ifndef CAST
		SUBSTITUTED,
		#endif
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

extern ty tydyn;
extern ty tyint;
extern ty tybool;
extern ty tyunit;
extern ty tyar;
extern ty tyli;

ty *(newty)();

#ifndef CAST
ty *(ty_find)(ty*);
#endif

#endif
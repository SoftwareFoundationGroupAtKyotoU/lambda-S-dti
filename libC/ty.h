#ifndef TY_H
#define TY_H

#ifndef STATIC
#include "types.h"

typedef struct ty {
	enum tykind : uint8_t {
		DYN, //0
		BASE_INT, //1
		BASE_BOOL, //2
		BASE_UNIT, //3
		TYFUN, //4
		TYLIST, //5
		TYTUPLE, //6
		TYVAR, //7
		#ifndef CAST
		SUBSTITUTED, //8
		#endif
	} tykind;
	union tydat {
		ty *tv;
		struct tyfun {
			ty *left;
			ty *right;
		} tyfun;
		ty *tylist;
		struct tytuple {
			uint16_t arity;
			ty **tys;
		} tytuple;
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
#endif //CAST

#endif //STATIC

#endif //TY_H
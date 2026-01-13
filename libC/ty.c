#include <gc.h>
#include "ty.h"

ty tydyn = { .tykind = DYN };
ty tyint = { .tykind = BASE_INT };
ty tybool = { .tykind = BASE_BOOL };
ty tyunit = { .tykind = BASE_UNIT };
ty tyar = { .tykind = TYFUN, .tydat = { .tyfun = { .left = &tydyn, .right = &tydyn } } };
ty tyli = { .tykind = TYLIST, .tydat = { .tylist = &tydyn } };

ty *newty() {
	ty *retty = (ty*)GC_MALLOC(sizeof(ty));
	retty->tykind = TYVAR;
	return retty;
}

#ifndef CAST
ty *ty_find(ty *t) {
    ty *root = t;
    while (root->tykind == SUBSTITUTED) {
        root = root->tydat.tv;
    }

    ty *curr = t;
    while (curr->tykind == SUBSTITUTED) {
        ty *next = curr->tydat.tv;
        curr->tydat.tv = root;
        curr = next;
    }

    return root;
}
#endif
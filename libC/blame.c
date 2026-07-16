#ifndef STATIC

#include <stdio.h>
#include <stdlib.h>

#include "types.h"

__attribute__((noreturn)) void blame(uint32_t rid, uint8_t polarity) {
	if(polarity == 1) {
		printf("Blame on the expression side:\n");
	} else {
		printf("Blame on the environment side:\n");
	}
	range r = range_list[rid];
	printf("%sline %d, character %d -- line %d, character %d\n", r.filename, r.startline, r.startchr, r.endline, r.endchr);
	exit(0);
}

#endif
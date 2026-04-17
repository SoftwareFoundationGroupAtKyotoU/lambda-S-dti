#if !defined(EAGER) && !defined(STATIC)
#include <stdlib.h>
#include "tpl.h"
#include "capp.h"
#include "ty.h"
#include "crc.h"

value tget(tpl *t, uint16_t i) {
    if (t->wrap) {
        tpl_wrap *tw = (tpl_wrap*)t;
        
        #ifdef CAST
        value inner_val = tget(tw->w, i);
        return cast(inner_val, tw->u1[i], tw->u2[i], tw->hdr.rid, tw->hdr.polarity);
        
        #else
        value inner_val = ((tpl_raw*)tw->w)->fields[i];
        return coerce(inner_val, tw->c->crcdat.tpl_crc.crcs[i]);
        #endif

    } else {
        tpl_raw *tr = (tpl_raw*)t;
        return tr->fields[i];
    }
}
#endif
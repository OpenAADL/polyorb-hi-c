#include <time.h>
#include "po_hi_types.h"

typedef struct {
    __po_hi_uint32_t     sec;     /* amount of second     */
    __po_hi_uint32_t     nsec;    /* amount of nanosecond */
} __po_hi_time_t;

/*@
  @ requires \valid(that);
  @*/
void test_struct_affectation(__po_hi_time_t *that) {
    __po_hi_time_t this;
    that->sec = this.sec;
    that->nsec = this.nsec;
    //@ assert that->sec == this.sec;
    //@ assert that->nsec == this.nsec;
}

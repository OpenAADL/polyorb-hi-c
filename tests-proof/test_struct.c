#include <time.h>
#include "po_hi_types.h"

typedef struct {
    __po_hi_uint32_t     sec;     /* amount of second     */
    __po_hi_uint32_t     nsec;    /* amount of nanosecond */
} __po_hi_time_t;

//@ ghost __po_hi_time_t *time_struct_to_be_initialized;

/*@
  @ ensures \separated(time_struct_to_be_initialized, __tp);
  @*/
int clock_gettime (clockid_t __clock_id, struct timespec *__tp);

/*@ requires \valid(mytime);
  @ ensures mytime->sec >=0;
  @ ensures mytime->nsec >=0 && mytime->nsec < 1000000000;
  @*/
void __po_hi_get_time(__po_hi_time_t *mytime)
{
    //@ ghost time_struct_to_be_initialized=mytime;

    struct timespec *ts;

    clock_gettime(0, ts);

    mytime->sec = ts->tv_sec;
    mytime->nsec = ts->tv_nsec;
}

#include <time.h>
#include "po_hi_types.h"

typedef struct {
   __po_hi_uint32_t     sec;     /* amount of second     */
   __po_hi_uint32_t     nsec;    /* amount of nanosecond */
} __po_hi_time_t;

/*@ requires \valid(mytime) && nvalue < 1000000000 && nvalue >= 0;
  @ ensures mytime->nsec < 1000000000;
  @*/
void __po_hi_get_time(__po_hi_time_t *mytime, long value, long nvalue)
{
  struct timespec ts;

  // this works!
  // ts.tv_nsec = nvalue;
  // ts.tv_sec = value;

  clock_gettime(0, &ts);

  //@ assert ts.tv_nsec < 1000000000;
  mytime->sec = ts.tv_sec;
  //@ assert ts.tv_nsec < 1000000000;
  mytime->nsec = ts.tv_nsec;
  //@ assert ts.tv_nsec < 1000000000;
  //@ assert mytime->nsec < 1000000000;
}

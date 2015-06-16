#include <stdio.h>
#include <po_hi_time.h>

int produce_data = 0;

void user_produce_spg (int* data)
{
   struct timespec mytime;
   clock_gettime (CLOCK_REALTIME, &mytime);
  *data = produce_data;
  printf ("At time %3lu:%3lu, produce : %d\n", mytime.tv_sec % 3600, mytime.tv_nsec/1000000,produce_data);
  produce_data++;
}

void user_consume_spg (int data)
{
   struct timespec mytime;
   clock_gettime (CLOCK_REALTIME, &mytime);
   printf( "At time %3lu:%3lu, consume : %d\n", mytime.tv_sec % 3600 , mytime.tv_nsec/1000000,data);
}

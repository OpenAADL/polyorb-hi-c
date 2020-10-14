#include <stdio.h>
#include <time.h>
#include <po_hi_time.h>

void user_produce_spg (int* data);
void user_consume_spg (int data);

void user_produce_spg (int* data)
{
  static int produce_data = 42;

#if defined (POSIX)
   struct timespec mytime;
   clock_gettime (CLOCK_REALTIME, &mytime);
   *data = produce_data;
   printf ("At time %3lu:%3lu, produce : %d\n",
           mytime.tv_sec % 3600, mytime.tv_nsec / 1000000,
           produce_data);
           fflush(stdout);
#else
   *data = produce_data;
   printf ("Produce %d\n", *data);
   fflush(stdout);
#endif
   produce_data++;
}

void user_consume_spg (int data)
{
#if defined (POSIX)
   struct timespec mytime;
   clock_gettime (CLOCK_REALTIME, &mytime);
   printf( "At time %3lu:%3lu, consume : %d\n", mytime.tv_sec % 3600 , mytime.tv_nsec/1000000,data);
   fflush(stdout);
#else
   printf ("Consume %d\n", data);
   fflush(stdout);
#endif

}

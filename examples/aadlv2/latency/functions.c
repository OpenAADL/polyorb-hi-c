#include <stdio.h>
#include <unistd.h>
#include <sys/time.h>

void sensor_emulator (int* value)
{
   struct timeval mytime;
   gettimeofday (&mytime, NULL);
   *value = ((mytime.tv_sec % 10) * 1000) + (mytime.tv_usec / 1000);
   printf( "I'm the sensor, I send value %d\n", *value);
}

void actuator_emulator (int value)
{
   struct timeval mytime;
   int val;

   gettimeofday (&mytime, NULL);
   val = ((mytime.tv_sec % 10) * 1000) + (mytime.tv_usec / 1000);
   printf("I'm actuator, I received value %d, current time=%d\n", value, val);
}

void spg1 (int ined, int* outed)
{
   struct timeval mytime;
   int val;
   gettimeofday (&mytime, NULL);
   val = ((mytime.tv_sec % 10) * 1000) + (mytime.tv_usec / 1000);
   printf ("I'm program 1, I received value %d, current sended time=%d\n", ined, val);
   *outed = val;
}

void spg2 (int ined, int* outed)
{
   struct timeval mytime;
   int val;
   gettimeofday (&mytime, NULL);
   val = ((mytime.tv_sec % 10) * 1000) + (mytime.tv_usec / 1000);
   printf ("I'm program 2, I received value %d, current sended time=%d\n", ined, val);
   *outed = val;
}

void spg3 (int ined, int* outed)
{
   struct timeval mytime;
   int val;
   gettimeofday (&mytime, NULL);
   val = ((mytime.tv_sec % 10) * 1000) + (mytime.tv_usec / 1000);
   printf ("I'm program 3, I received value %d, current sended time=%d\n", ined, val);
   *outed = val;
}

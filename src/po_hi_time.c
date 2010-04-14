/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#include <time.h>
#include <pthread.h>
#include <errno.h>

#include <po_hi_config.h>
#include <po_hi_time.h>
#include <po_hi_returns.h>

#ifdef NEED_CLOCK_GETTIME
#include <sys/time.h>
int clock_gettime(int clk_id, struct timespec *tp)
{
   struct timeval now;
   int rv = gettimeofday(&now, NULL);

   if (rv != 0) 
   {
      return rv;
   }

   tp->tv_sec = now.tv_sec;
   tp->tv_nsec = now.tv_usec * 1000;

   return 0;
}
#endif


int __po_hi_get_time (__po_hi_time_t* mytime)
{
   struct timespec ts;
   __po_hi_time_t tmp;

   if (clock_gettime (CLOCK_REALTIME, &ts)!=0)
   {
      return (__PO_HI_ERROR_CLOCK);
   }
   tmp = ts.tv_sec;
   tmp = tmp * 1000000;
   tmp += ts.tv_nsec / 1000;
   *mytime = tmp;

   return (__PO_HI_SUCCESS);
}

__po_hi_time_t __po_hi_add_times (__po_hi_time_t left, __po_hi_time_t right)
{
   __po_hi_time_t rtime;
   rtime = left + right;
   return (rtime);
}

__po_hi_time_t __po_hi_seconds (__po_hi_uint32_t seconds)
{
   __po_hi_time_t mytime;
   mytime = seconds * 1000000;
   return (mytime);
}

__po_hi_time_t __po_hi_milliseconds (__po_hi_uint32_t milliseconds)
{
   __po_hi_time_t mytime;
   mytime = milliseconds * 1000;
   return (mytime);
}

__po_hi_time_t __po_hi_microseconds (__po_hi_uint32_t microseconds)
{
   __po_hi_time_t mytime;
   mytime = microseconds;
   return (mytime);
}

int __po_hi_delay_until (__po_hi_time_t time)
{
   pthread_mutex_t mutex;
   pthread_cond_t cond;
   struct timespec timer;
   int ret;

   timer.tv_sec = time / 1000000;

   timer.tv_nsec = (time - (timer.tv_sec*1000000)) * 1000;

   if (pthread_mutex_init (&mutex, NULL) != 0)
   {
      return (__PO_HI_ERROR_PTHREAD_MUTEX);
   }

   if (pthread_cond_init (&cond, NULL) != 0)
   {
      pthread_mutex_destroy (&mutex);
      return (__PO_HI_ERROR_PTHREAD_COND);
   }

   pthread_mutex_lock (&mutex);

   ret = pthread_cond_timedwait (&cond, &mutex, &timer);

   if ( (ret != 0) && (ret != ETIMEDOUT))
   {
      ret = __PO_HI_ERROR_PTHREAD_COND;
   }
   else
   {
      ret = __PO_HI_SUCCESS;
   }

   pthread_mutex_unlock (&mutex);

   if (pthread_cond_destroy (&cond) != 0)
   {
      ret = __PO_HI_ERROR_PTHREAD_COND;
   }

   if (pthread_mutex_destroy (&mutex) != 0)
   {
      ret = __PO_HI_ERROR_PTHREAD_MUTEX;
   }
   return (ret);
}

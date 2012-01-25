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
#include <errno.h>

#include <po_hi_config.h>
#include <po_hi_time.h>
#include <po_hi_returns.h>
#include <po_hi_debug.h>

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
#include <pthread.h>
#elif defined (RTEMS_PURE)
#include <bsp.h>
#endif 

#if defined (POSIX) && defined (NEED_CLOCK_GETTIME)
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
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   struct timespec ts;

   if (clock_gettime (CLOCK_REALTIME, &ts)!=0)
   {
      return (__PO_HI_ERROR_CLOCK);
   }
   
   mytime->sec    = ts.tv_sec;
   mytime->nsec   = ts.tv_nsec;

   return (__PO_HI_SUCCESS);
#elif defined (RTEMS_PURE)
   rtems_time_of_day    current_time;

   if (rtems_clock_get (RTEMS_CLOCK_GET_TOD, &current_time) != RTEMS_SUCCESSFUL)
   {
      __DEBUGMSG ("Error when trying to get the clock on RTEMS\n");
   }

   mytime->sec  = _TOD_To_seconds (&current_time);
   mytime->nsec =  current_time.ticks * rtems_configuration_get_microseconds_per_tick() * 1000;

   return (__PO_HI_SUCCESS);
#elif defined (XENO_NATIVE)
   mytime->sec  = rt_timer_tsc2ns (rt_timer_read ()) / 1000000000;
   mytime->nsec =  rt_timer_tsc2ns (rt_timer_read ()) - (mytime->sec * 1000000000);
   return (__PO_HI_SUCCESS);
#else
   return (__PO_HI_UNAVAILABLE);
#endif
}

int __po_hi_add_times (__po_hi_time_t* result, const __po_hi_time_t* left, const __po_hi_time_t* right)
{
   result->sec    = left->sec + right->sec;
   result->nsec   = left->nsec + right->nsec;
   if (result->nsec > 1000000000)
   {
      result->sec = result->sec + 1;
      result->nsec = result->nsec - 1000000000;
   }
   return 1;
}

int __po_hi_seconds (__po_hi_time_t* time, const __po_hi_uint32_t seconds)
{
   time->sec    = seconds;
   time->nsec   = 0;
   return 1;
}

int __po_hi_milliseconds (__po_hi_time_t* time, const __po_hi_uint32_t milliseconds)
{
   time->sec    = milliseconds / 1000;
   time->nsec   = (milliseconds - (time->sec * 1000)) * 1000000;
   return 1;
}

int __po_hi_microseconds (__po_hi_time_t* time, const __po_hi_uint32_t microseconds)
{
   time->sec    = microseconds / 1000000;
   time->nsec   = (microseconds - (time->sec * 1000000)) * 1000;
   return 1;
}

int __po_hi_delay_until (const __po_hi_time_t* time)
{
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   pthread_mutex_t mutex;
   pthread_cond_t cond;
   struct timespec timer;
   int ret;

   timer.tv_sec = time->sec;

   timer.tv_nsec = time->nsec;

   if (pthread_mutex_init (&mutex, NULL) != 0)
   {
      __PO_HI_DEBUG_INFO ("[TIME] __po_hi_delay_until: cannot initialize mutex\n");
      return (__PO_HI_ERROR_PTHREAD_MUTEX);
   }

   if (pthread_cond_init (&cond, NULL) != 0)
   {
      __PO_HI_DEBUG_INFO ("[TIME] __po_hi_delay_until: cannot initialize cond\n");
      pthread_mutex_destroy (&mutex);
      return (__PO_HI_ERROR_PTHREAD_COND);
   }

   pthread_mutex_lock (&mutex);

   ret = pthread_cond_timedwait (&cond, &mutex, &timer);

   if ( (ret != 0) && (ret != ETIMEDOUT))
   {
      __PO_HI_DEBUG_INFO ("[TIME] __po_hi_delay_until: delay until error\n");
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
#elif defined (RTEMS_PURE)
   return (__PO_HI_UNAVAILABLE);
#elif defined (XENO_NATIVE)
  int ret;
  ret =  rt_task_sleep_until (rt_timer_ns2tsc ( (time->sec * 1000000000) +  time->nsec));
  if (ret)
  {
      __DEBUGMSG ("[TASK] Error in rt_task_sleep_until, ret=%d\n", ret);
      return (__PO_HI_ERROR_PTHREAD_COND);
  }
  return (__PO_HI_SUCCESS);
#else
   return (__PO_HI_UNAVAILABLE);
#endif
}

int __po_hi_time_is_greater (const __po_hi_time_t* value, const __po_hi_time_t* limit)
{
   if (value->sec > limit->sec)
   {
      return 1;
   }
   if (value->sec == limit->sec)
   {
      if (value->nsec > limit->nsec)
      {
         return 1;
      }
   }
   return 0;
}

int __po_hi_time_copy (__po_hi_time_t* dst, const __po_hi_time_t* src)
{
   dst->sec = src->sec;
   dst->nsec = src->nsec;
   return (__PO_HI_SUCCESS);
}



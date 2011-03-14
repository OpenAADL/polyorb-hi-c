/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2010-2011, European Space Agency (ESA).
 */


#include <deployment.h>
/* included files from the generated code */

#include <po_hi_config.h>
#include <po_hi_common.h>
#include <po_hi_returns.h>
#include <po_hi_task.h>
#include <po_hi_debug.h>
#include <po_hi_protected.h>
/* included files from PolyORB-HI-C */

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
#include <pthread.h>
/* POSIX files */

pthread_cond_t cond_init;
pthread_mutex_t mutex_init;
#endif

#ifdef RTEMS_PURE
rtems_id __po_hi_main_initialization_barrier;
#endif

#if defined (XENO_NATIVE)
#include <native/cond.h>
#include <native/mutex.h>
RT_COND   cond_init;
RT_MUTEX  mutex_init;
#endif



int initialized_tasks = 0;
/* The barrier is initialized with __PO_HI_NB_TASKS +1
 * members, because the main function must pass the barrier
 */
int nb_tasks_to_init = __PO_HI_NB_TASKS + 1;

void __po_hi_initialize_add_task ()
{
      __DEBUGMSG ("[MAIN] Add a task to initialize\n");
      nb_tasks_to_init++;
}

int __po_hi_initialize ()
{
#if defined (XENO_POSIX) || defined (XENO_NATIVE)
   /*
    * Once initialization has been done, we avoid ALL 
    * potential paging operations that can introduce
    * some indeterministic timing behavior.
    */

   #include <sys/mman.h>
   mlockall(MCL_CURRENT|MCL_FUTURE);
#endif

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   pthread_mutexattr_t mutex_attr;
   if (pthread_mutexattr_init (&mutex_attr) != 0)
   {
      __DEBUGMSG ("[MAIN] Unable to init mutex attributes\n");
   }

#ifdef RTEMS_POSIX
   if (pthread_mutexattr_setprioceiling (&mutex_attr, 50) != 0)
   {
      __DEBUGMSG ("[MAIN] Unable to set priority ceiling on mutex\n");
   }
#endif

   if (pthread_mutex_init (&mutex_init, &mutex_attr) != 0 )
    {
      __DEBUGMSG ("[MAIN] Unable to init pthread_mutex\n");
      return (__PO_HI_ERROR_PTHREAD_MUTEX);
    }

  __DEBUGMSG ("[MAIN] Have %d tasks to init\n", nb_tasks_to_init);

  if (pthread_cond_init (&cond_init, NULL) != 0)
  {
     return (__PO_HI_ERROR_PTHREAD_COND);
  }
#endif

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   pthread_mutexattr_t mutex_attr;
   if (pthread_mutexattr_init (&mutex_attr) != 0)
   {
      __DEBUGMSG ("[MAIN] Unable to init mutex attributes\n");
   }

#ifdef RTEMS_POSIX
   if (pthread_mutexattr_setprioceiling (&mutex_attr, 50) != 0)
   {
      __DEBUGMSG ("[MAIN] Unable to set priority ceiling on mutex\n");
   }
#endif

   if (pthread_mutex_init (&mutex_init, &mutex_attr) != 0 )
    {
      __DEBUGMSG ("[MAIN] Unable to init pthread_mutex\n");
      return (__PO_HI_ERROR_PTHREAD_MUTEX);
    }

  __DEBUGMSG ("[MAIN] Have %d tasks to init\n", nb_tasks_to_init);

  if (pthread_cond_init (&cond_init, NULL) != 0)
  {
     return (__PO_HI_ERROR_PTHREAD_COND);
  }

#endif

#if defined (XENO_NATIVE)
   if (rt_cond_create (&cond_init, NULL))
   {
      __DEBUGMSG ("[MAIN] Unable to init the initialization condition variable \n");
      return (__PO_HI_ERROR_PTHREAD_MUTEX);
   }

  if (rt_mutex_create (&mutex_init, NULL) != 0)
  {
      __DEBUGMSG ("[MAIN] Unable to init the initialization mutex variable \n");
     return (__PO_HI_ERROR_PTHREAD_COND);
  }
#endif


#if defined (RTEMS_POSIX) || defined (RTEMS_PURE)
#include <rtems/rtems/clock.h>
  rtems_status_code ret;
  rtems_time_of_day time;

  time.year   = 1988;
  time.month  = 12;
  time.day    = 31;
  time.hour   = 9;
  time.minute = 1;
  time.second = 10;
  time.ticks  = 0;

  ret = rtems_clock_set( &time );
  if (ret != RTEMS_SUCCESSFUL)
  {
     __DEBUGMSG ("[MAIN] Cannot set the clock\n");
     return __PO_HI_ERROR_CLOCK;
  }
#endif

#ifdef RTEMS_PURE
  __DEBUGMSG ("[MAIN] Create a barrier that wait for %d tasks\n", nb_tasks_to_init);
   
  ret = rtems_barrier_create (rtems_build_name ('B', 'A', 'R', 'M'), RTEMS_BARRIER_AUTOMATIC_RELEASE, nb_tasks_to_init, &__po_hi_main_initialization_barrier);
  if (ret != RTEMS_SUCCESSFUL)
  {
     __DEBUGMSG ("[MAIN] Cannot create the main barrier, return code=%d\n", ret);
  }
#endif

  __po_hi_initialize_tasking ();

  /* Initialize protected objects */
#if __PO_HI_NB_PROTECTED > 0
  __po_hi_protected_init();
#endif

  return (__PO_HI_SUCCESS);
}

int __po_hi_wait_initialization ()
{
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   int cstate;
   if (pthread_setcancelstate (PTHREAD_CANCEL_ENABLE, &cstate) != 0)
   {
      __DEBUGMSG ("[MAIN] Cannot modify the cancel state\n");
   }

   if (pthread_setcanceltype (PTHREAD_CANCEL_ASYNCHRONOUS, &cstate) != 0)
   {
      __DEBUGMSG ("[MAIN] Cannot modify the cancel type\n");
   }

  if (pthread_mutex_lock (&mutex_init) != 0)
  {
    return (__PO_HI_ERROR_PTHREAD_MUTEX);
  }

  initialized_tasks++;

  __DEBUGMSG ("[MAIN] %d task(s) initialized (total to init =%d)\n", initialized_tasks, nb_tasks_to_init);
 
  while (initialized_tasks < nb_tasks_to_init)
  {
      pthread_cond_wait (&cond_init, &mutex_init);
  }
  pthread_cond_broadcast (&cond_init);
  pthread_mutex_unlock (&mutex_init);
  return (__PO_HI_SUCCESS);
#elif defined (RTEMS_PURE) 
  rtems_status_code ret;

  __DEBUGMSG ("[MAIN] Task wait for the barrier\n");
  ret = rtems_barrier_wait (__po_hi_main_initialization_barrier, RTEMS_WAIT);
  if (ret != RTEMS_SUCCESSFUL)
  {
     __DEBUGMSG ("[MAIN] Error while waiting for the barrier, return code=%d\n", ret);
     return (__PO_HI_ERROR_UNKNOWN);
  }
  __DEBUGMSG ("[MAIN] Task release the barrier\n");
  return (__PO_HI_SUCCESS);
#elif defined (XENO_NATIVE)
  int ret;
  ret = rt_mutex_acquire (&mutex_init, TM_INFINITE);
  if (ret != 0)
  {
   __DEBUGMSG ("[MAIN] Cannot acquire mutex (return code = %d)\n", ret);
    return (__PO_HI_ERROR_PTHREAD_MUTEX);
  }

  initialized_tasks++;

  __DEBUGMSG ("[MAIN] %d task(s) initialized (total to init =%d)\n", initialized_tasks, nb_tasks_to_init);
 
  while (initialized_tasks < nb_tasks_to_init)
  {
      rt_cond_wait (&cond_init, &mutex_init, TM_INFINITE);
  }
  rt_cond_broadcast (&cond_init);
  rt_mutex_release (&mutex_init);
  return (__PO_HI_SUCCESS);

#else
  return (__PO_HI_UNAVAILABLE);
#endif
}

#ifdef __PO_HI_USE_GPROF
void __po_hi_wait_end_of_instrumentation ()
{
#ifdef RTEMS_PURE
   rtems_task_wake_after (10000000 / _TOD_Microseconds_per_tick); 
#else
   #include <po_hi_time.h> 
   #include <unistd.h>

   __po_hi_time_t now;
   __po_hi_get_time (&now);
   __po_hi_delay_until (__po_hi_add_times (now, __po_hi_seconds (10)));
#endif
  __DEBUGMSG ("Call exit()\n");
  __po_hi_tasks_killall ();
   exit (1);

  __DEBUGMSG ("exit() called\n");
#ifdef RTEMS_PURE
  rtems_task_delete (rtems_self ());
#endif
}
#endif

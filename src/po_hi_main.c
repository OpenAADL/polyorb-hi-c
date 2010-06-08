/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2009, GET-Telecom Paris.
 * Copyright (C) 2010, European Space Agency (ESA)
 */

#include <pthread.h>
/* POSIX files */

#include <deployment.h>
/* included files from the generated code */

#include <po_hi_config.h>
#include <po_hi_common.h>
#include <po_hi_returns.h>
#include <po_hi_task.h>
#include <po_hi_debug.h>
#include <po_hi_protected.h>
/* included files from PolyORB-HI-C */

pthread_cond_t cond_init;
pthread_mutex_t mutex_init;

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
   pthread_mutexattr_t mutex_attr;

#ifdef RTEMS_POSIX
#include <rtems/rtems/clock.h>
  rtems_status_code status;
  rtems_time_of_day time;

  time.year   = 1988;
  time.month  = 12;
  time.day    = 31;
  time.hour   = 9;
  time.minute = 0;
  time.second = 0;
  time.ticks  = 0;

  status = rtems_clock_set( &time );
  
#endif

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

  __po_hi_initialize_tasking ();

  /* Initialize protected objects */
#if __PO_HI_NB_PROTECTED > 0
  __po_hi_protected_init();
#endif

  return (__PO_HI_SUCCESS);
}

int __po_hi_wait_initialization ()
{
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
}

#ifdef __PO_HI_USE_GPROF
void __po_hi_wait_end_of_instrumentation ()
{
   #include <po_hi_time.h> 
   #include <unistd.h>

   __po_hi_time_t now;
   __po_hi_get_time (&now);
   __po_hi_delay_until (__po_hi_add_times (now, __po_hi_seconds (10)));
  __DEBUGMSG ("Call exit()\n");
   exit (1);

  __DEBUGMSG ("exit() called\n");
}
#endif


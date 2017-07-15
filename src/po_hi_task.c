/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2017 ESA & ISAE.
 */

#if defined (__linux__) || defined (RTEMS412)
/*  We need GNU extensions to support thread affinify.
    These are Linux or RTEMS specific
 */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE 1
#endif /* _GNU_SOURCE */
#endif /* __linux__ || RTEMS412 */

#ifdef __linux__
#include <sched.h>
#endif /* __linux__ */

#if defined (SIMULATOR)
#include <um_threads.h>
#undef POSIX
#endif

#if defined (RTEMS_POSIX) || defined (RTEMS_PURE)
#ifdef RTEMS412
#include <sys/cpuset.h>
#endif
#endif

#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
#if defined (__CYGWIN__) || defined (__MINGW32__) || defined (RTEMS_POSIX) || defined (RTEMS_PURE)
#else
#include <xlocale.h>
#include <unistd.h>
#endif

#include <pthread.h>
#include <sched.h>
#endif

#if defined (_WIN32)
#include <tchar.h>
#include <windows.h>
#endif

#include <errno.h>
/* Headers from the executive */

#include <po_hi_config.h>
#include <po_hi_time.h>
#include <po_hi_task.h>
#include <po_hi_debug.h>
#include <po_hi_returns.h>
#include <po_hi_types.h>
#include <po_hi_utils.h>
/* Header files in PolyORB-HI */

#if defined (MONITORING)
#include <trace_manager.hh>
#endif
/* Headers from run-time verification */

#include <deployment.h>
/* Header files from generated code */

typedef enum __po_hi_task_category_t { TASK_PERIODIC, TASK_SPORADIC, TASK_BACKGROUND }
    __po_hi_task_category;


int nb_tasks; /* number of created tasks */

typedef struct
{
  __po_hi_task_id     id;       /* Identifier of the task in the system */
  __po_hi_task_category task_category;
  __po_hi_time_t      period;
  __po_hi_time_t      offset;

#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
  __po_hi_time_t      timer;
#if defined (_WIN32)
  DWORD tid;
#else
  pthread_t           tid;              /* The pthread_t type used by the
                                           POSIX library */
#endif
  pthread_mutex_t     mutex;
  pthread_cond_t      cond;
#elif defined (_WIN32)
  __po_hi_time_t      timer;
  DWORD               tid;
#elif defined (RTEMS_PURE)
  rtems_id            ratemon_period;
  rtems_id            rtems_id;
#elif defined(XENO_NATIVE)
  RT_TASK             xeno_id;
#elif defined(SIMULATOR)
  um_thread_id        um_id;
#endif
} __po_hi_task_t;
/*
 * Structure of a task, contains platform-dependent members
 */

__po_hi_task_t tasks[__PO_HI_NB_TASKS];
/* Array which contains all tasks informations */

#if defined (_WIN32)
HANDLE  __po_hi_tasks_array[__PO_HI_NB_TASKS];
#endif

__po_hi_task_id __po_hi_get_task_id (void) {

#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
  pthread_t pthread_id = pthread_self();
  int i;

  for (i = 0; i < __PO_HI_NB_TASKS; i++) {
    if (pthread_id == tasks[i].tid) {
      return tasks[i].id;
    }
  }
#endif

  return (__PO_HI_ERROR_UNKNOWN);

}

void __po_hi_wait_for_tasks ()
{
#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
  int i;

  for (i = 0; i < __PO_HI_NB_TASKS; i++)
    {
      pthread_join( tasks[i].tid , NULL );
    }

#elif defined (RTEMS_PURE)
  rtems_task_suspend(RTEMS_SELF);

#elif defined (_WIN32)
  WaitForMultipleObjects (__PO_HI_NB_TASKS, __po_hi_tasks_array, TRUE, INFINITE);

#elif defined (XENO_NATIVE)
  int ret;
  while (1)
  {
    ret = rt_task_join (&(tasks[0].xeno_id));
    if (ret != 0)
      {
        __PO_HI_DEBUG_CRITICAL ("Error while calling rt_task_suspend in __po_hi_wait_for_tasks (ret=%d)\n", ret);
      }
  }
#elif defined (SIMULATOR)
  start_scheduler();
  return (__PO_HI_SUCCESS);

#endif

#ifdef __PO_HI_DEBUG
   while (1)
   {
      __DEBUGMSG ("Should NEVER be called !!!\n");
   }
#endif
}

/*
 * compute next period for a task
 * The argument is the task-id
 * The task must be a cyclic task (periodic or sporadic)
 */
int __po_hi_compute_next_period (__po_hi_task_id task)
{
#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX) || defined (_WIN32)

    /* If we call this function for the first time, we need to configure
       the initial timer to epoch */
  if (tasks[task].timer.sec == 0 && tasks[task].timer.nsec == 0) {
    tasks[task].timer = get_epoch();
    __po_hi_add_times(&(tasks[task].timer), &(tasks[task].timer), &tasks[task].offset);
    return (__PO_HI_SUCCESS);
  }

  /* Otherwise, we increment either using an absoulte timeline
     (periodic), or relative to the latest dispatch time (sporadic task) */

  switch (tasks[task].task_category) {
  case TASK_PERIODIC:
    __po_hi_add_times(&(tasks[task].timer), &(tasks[task].timer), &tasks[task].period );
    break;

  case TASK_SPORADIC: {
      __po_hi_time_t mytime;

      if (__po_hi_get_time (&mytime) != __PO_HI_SUCCESS) {
        return (__PO_HI_ERROR_CLOCK);
      }

      __po_hi_add_times(&(tasks[task].timer), &mytime, &tasks[task].period );
      break;
   }
  case TASK_BACKGROUND:
    break;
  }

  return (__PO_HI_SUCCESS);

#elif defined (RTEMS_PURE)
   rtems_status_code ret;
   rtems_name name;

   if (tasks[task].ratemon_period == RTEMS_INVALID_ID)
   {
      name = rtems_build_name ('P', 'R', 'D' + (char)task, ' ');

      __DEBUGMSG ("Create monotonic server for task %d\n", task);
      ret = rtems_rate_monotonic_create (name, &(tasks[task].ratemon_period));
      if (ret != RTEMS_SUCCESSFUL)
      {
         __DEBUGMSG ("Error while creating the monotonic server, task=%d, status=%d\n", task, ret);
      }
   }
  return (__PO_HI_SUCCESS);
#elif defined (XENO_NATIVE)

  /*
   * In XENO_NATIVE target, we don't need to recompute the next period
   * since the API provides functionnalities to do it automatically.
   */

  return (__PO_HI_SUCCESS);
#else
   return (__PO_HI_UNAVAILABLE);
#endif
}


int __po_hi_wait_for_next_period (__po_hi_task_id task)
{

/*!
 * Entry ports monitoring at dispatch if MONITORING is defined
 */
#if defined (MONITORING)
  update_periodic_dispatch(task); // XXX ?
#endif

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
  int ret;
   __PO_HI_INSTRUMENTATION_VCD_WRITE("0t%d\n", task);
  __po_hi_task_delay_until (&(tasks[task].timer), task);

  if ( (ret = __po_hi_compute_next_period (task)) != 1)
    {
      return (__PO_HI_ERROR_CLOCK);
    }

   __PO_HI_INSTRUMENTATION_VCD_WRITE("1t%d\n", task);

  return (__PO_HI_SUCCESS);

#elif defined (_WIN32)
  int ret;
  __po_hi_task_delay_until (&(tasks[task].timer), task);
  if ( (ret = __po_hi_compute_next_period (task)) != 1)
    {
      return (__PO_HI_ERROR_CLOCK);
    }

  return (__PO_HI_SUCCESS);

#elif defined (RTEMS_PURE)
   rtems_status_code ret;
   ret = rtems_rate_monotonic_period (tasks[task].ratemon_period, (rtems_interval)__PO_HI_TIME_TO_US(tasks[task].period) / rtems_configuration_get_microseconds_per_tick());
   /*
   ret = rtems_rate_monotonic_period (tasks[task].ratemon_period, tasks[task].period / _TOD_Microseconds_per_tick);
   */

   switch (ret)
   {
      case RTEMS_SUCCESSFUL:
         return (__PO_HI_SUCCESS);
         break;
      case RTEMS_TIMEOUT:
         __DEBUGMSG ("Error in rtems_rate_monotonic_period (TIMEOUT, task = %d)\n", task);
         return (__PO_HI_ERROR_TASK_PERIOD);
         break;
      default:
         __DEBUGMSG ("Error in rtems_rate_monotonic_period (unknown, error code=%d, task=%d)\n", ret, task);
         return (__PO_HI_ERROR_UNKNOWN);
         break;
   }

   return (__PO_HI_UNAVAILABLE);

#elif defined (XENO_NATIVE)
   unsigned long overrun;
   int ret;
   ret = rt_task_wait_period (&overrun);
   if ( ret != 0)
   {
         __DEBUGMSG ("Error in rt_task_period (task=%d;ret=%d,overrun=%lu)\n", task, ret, overrun);
         return (__PO_HI_ERROR_TASK_PERIOD);
   }

   if (overrun != 0)
   {
      return (__PO_HI_ERROR_TASK_PERIOD);
   }

   return (__PO_HI_SUCCESS);
#else
  return (__PO_HI_UNAVAILABLE);
#endif
}

int __po_hi_initialize_tasking( )
{
  int i;

  for (i = 0; i < __PO_HI_NB_TASKS; i++)
  {
     __po_hi_seconds (&(tasks[i].period), 0);
     tasks[i].id     = invalid_task_id;
#ifdef RTEMS_PURE
      tasks[i].ratemon_period = RTEMS_INVALID_ID;
#endif
  }

  nb_tasks = 0;

  return (__PO_HI_SUCCESS);
}

/*
 * For multi-core aware systems, this function returns the number of
 * core available
 */

#if defined (POSIX) || defined (RTEMS_POSIX)
int __po_hi_number_of_cpus (void)
{
  int cores = 1;

#if defined (__linux__)  || defined (__APPLE__)

  cores = (int) sysconf (_SC_NPROCESSORS_ONLN);
#endif

  return cores;
}

#endif

/*
 * For each kind of system, we declare a generic function that
 * create a thread. For POSIX-compliant systems, the function
 * is called __po_hi_posix_create_thread
 */

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
pthread_t __po_hi_posix_create_thread (__po_hi_priority_t priority,
                                       __po_hi_stack_t    stack_size,
                                       const __po_hi_int8_t       core_id,
                                       void*              (*start_routine)(void),
                                       void*              arg)
{
  int                policy;
  pthread_t          tid;
  pthread_attr_t     attr;
  struct sched_param param;
  int err;

  /* Create attributes to store all configuration parameters */

  if (pthread_attr_init (&attr) != 0)
    {
      return ((pthread_t)__PO_HI_ERROR_PTHREAD_ATTR);
    }

#if (defined (POSIX) && defined (__linux__))

  /* The following is disabled pending further investigation on affinity support in 4.11.99 */
  /*|| (defined (RTEMS_POSIX) && defined (RTEMS412))) */

#ifndef __COMPCERT__
  /* Thread affinity */
  cpu_set_t cpuset;

  if ( core_id > __po_hi_number_of_cpus() )
    {
      __PO_HI_DEBUG_CRITICAL("Invalid CPU core id\n");
      return ((pthread_t)__PO_HI_ERROR_PTHREAD_ATTR);
    }

  CPU_ZERO(&cpuset);
  CPU_SET(core_id, &cpuset);

  if (pthread_attr_setaffinity_np(&attr, sizeof(cpuset), &cpuset) != 0)
    {
      __DEBUGMSG("CANNOT SET AFFINTY\n");
      return ((pthread_t)__PO_HI_ERROR_PTHREAD_ATTR);
    }
#else
#warning pthread_affinity managmeent disabled for Compcert
#endif

#else
  if ( core_id != 0 )
    {
      __PO_HI_DEBUG_CRITICAL("This platform does not support CPU affinity setting\n");
      return ((pthread_t)__PO_HI_ERROR_PTHREAD_ATTR);
    }

#endif

#if defined (POSIX) || defined (XENO_POSIX)
  if (pthread_attr_setscope (&attr, PTHREAD_SCOPE_SYSTEM) != 0)
    {
      return ((pthread_t)__PO_HI_ERROR_PTHREAD_ATTR);
    }
#elif defined (RTEMS_POSIX)
  if (pthread_attr_setscope (&attr, PTHREAD_SCOPE_PROCESS) != 0)
  {
    return ((pthread_t)__PO_HI_ERROR_PTHREAD_ATTR);
  }
#endif

  if (stack_size != 0)
    {
      if (pthread_attr_setstacksize (&attr, stack_size) != 0)
	{
	  return ((pthread_t)__PO_HI_ERROR_PTHREAD_ATTR);
        }
    }

    err = pthread_create (&tid, &attr, (void* (*)(void*))start_routine, arg);
    if (err != 0)
    {
      __PO_HI_DEBUG_CRITICAL ("Thread creation failed - pthread_create returned %d\n", err);
      return ((pthread_t)__PO_HI_ERROR_PTHREAD_CREATE);
    }

  policy = SCHED_FIFO;
  param.sched_priority = priority;

#ifdef __PO_HI_DEBUG
  if (priority < sched_get_priority_min (policy))
  {
      __DEBUGMSG("PRIORITY IS TOO LOW\n");
  }

  if (priority > sched_get_priority_max (policy))
  {
      __DEBUGMSG("PRIORITY IS TOO HIGH\n");
  }
#endif

  /*
   * We print a message that the user has to be root on
   * its computer. In fact, most of the time, the
   * function pthread_setschedparam fails because
   * the user is not root. On many systems, only root
   * can change the priority of the threads.
   */
  __DEBUGMSG("ABOUT TO SET PRIORITY FOR TASK %d\n" , nb_tasks );
  if (pthread_setschedparam (tid, policy, &param)!=0)
    {
      __DEBUGMSG("CANNOT SET PRIORITY FOR TASK %d\n" , nb_tasks );
      __DEBUGMSG("IF YOU ARE USING POSIX IMPLEMENTATION\n");
      __DEBUGMSG("BE SURE TO BE LOGGED AS ROOT\n");
    }

  return tid;
}


int __po_hi_posix_initialize_task (__po_hi_task_t* task)
{
  if (pthread_mutex_init (&(task->mutex), NULL) != 0)
    {
      return (__PO_HI_ERROR_PTHREAD_MUTEX);
    }

  if (pthread_cond_init (&(task->cond), NULL) != 0)
    {
      return (__PO_HI_ERROR_PTHREAD_COND);
    }

  return (__PO_HI_SUCCESS);
}

#endif /* POSIX || RTEMS_POSIX */

#if defined (_WIN32)
DWORD __po_hi_win32_create_thread (__po_hi_task_id    id,
                                   __po_hi_priority_t priority,
                                   __po_hi_stack_t    stack_size,
                                   void*              (*start_routine)(void),
                                   void*              arg)
{
   DWORD tid;
   HANDLE h;
   h = CreateThread (NULL, 0, (LPTHREAD_START_ROUTINE) start_routine, NULL, 0, &tid);
   __po_hi_tasks_array[id] = h;
   return tid;
}
#endif

#ifdef RTEMS_PURE
rtems_id __po_hi_rtems_create_thread (__po_hi_priority_t priority,
                                      __po_hi_stack_t    stack_size,
                                      __po_hi_int8_t       core_id,
                                      void*              (*start_routine)(void),
                                      void*              arg)
{
  rtems_id rid;
  if (rtems_task_create (rtems_build_name( 'T', 'A', nb_tasks, ' ' ),
                         1,
                         RTEMS_MINIMUM_STACK_SIZE,
                         RTEMS_DEFAULT_MODES,
                         RTEMS_DEFAULT_ATTRIBUTES | RTEMS_FLOATING_POINT, &rid)
      != RTEMS_SUCCESSFUL)
    {
      __DEBUGMSG ("ERROR when creating the task\n");
      return __PO_HI_ERROR_CREATE_TASK;
    }

#ifdef RTEMS412
  /* Thread affinity API for SMP systems appeared in RTEMS 4.11,
     section 25 of RTEMS Applications C User's Guide .
  */

  cpu_set_t         cpuset;

  CPU_ZERO(&cpuset);
  CPU_SET(core_id, &cpuset);

  if (rtems_task_set_affinity(rid, sizeof(cpuset), &cpuset) != RTEMS_SUCCESSFUL)
    {
      __DEBUGMSG ("ERROR setting thread affinity\n");
      return __PO_HI_ERROR_CREATE_TASK;
    }
#endif

  if (rtems_task_start (rid, (rtems_task_entry)start_routine, 0 ) != RTEMS_SUCCESSFUL)
    {
      __DEBUGMSG ("ERROR when starting the task\n");
      return __PO_HI_ERROR_CREATE_TASK;
    }

   return rid;
}
#endif

#ifdef XENO_NATIVE
RT_TASK __po_hi_xenomai_create_thread (__po_hi_priority_t priority,
                                       __po_hi_stack_t    stack_size,
                                       void*              (*start_routine)(void),
                                       void*              arg)
{
   RT_TASK newtask;

   /*
    * Uses T_JOINABLE at this time, should avoid that later and put 0 instead
    * to be able to use kernel-based threads.
    */

   if (rt_task_create (&newtask, NULL, stack_size, priority, T_JOINABLE))
   {
      __DEBUGMSG ("ERROR when creating the task\n");
   }
   return newtask;
}
#endif

int __po_hi_create_generic_task (const __po_hi_task_id      id,
                                 const __po_hi_time_t*      period,
                                 const __po_hi_priority_t   priority,
                                 const __po_hi_stack_t      stack_size,
                                 const __po_hi_int8_t       core_id,
                                 void*                      (*start_routine)(void),
                                 void*                      arg)
{

  if (id == -1)
    {
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
      __po_hi_posix_create_thread (priority, stack_size, core_id, start_routine, arg);
      return (__PO_HI_SUCCESS);
#elif defined (_WIN32)
      __po_hi_win32_create_thread (id, priority, stack_size, start_routine, arg);
      return (__PO_HI_SUCCESS);
#elif defined (XENO_NATIVE)
      RT_TASK t;
      (void) arg;
      t = __po_hi_xenomai_create_thread (priority, stack_size, start_routine, arg);
      if (rt_task_start (&(t), (void*)start_routine, NULL))
      {
         __DEBUGMSG ("ERROR when starting the task\n");
      }
      return (__PO_HI_SUCCESS);
#elif defined (RTEMS_PURE)
      (void) arg;
      __po_hi_rtems_create_thread (priority, stack_size, core_id, start_routine, arg);
      return (__PO_HI_SUCCESS);
#else
      return (__PO_HI_UNAVAILABLE);
#endif
    }
  else
    {
      __po_hi_task_t* my_task;
      my_task         = &(tasks[id]);
      __po_hi_time_copy (&(my_task->period), period);
      my_task->id     = id;

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
      my_task->tid    = __po_hi_posix_create_thread
        (priority, stack_size, core_id, start_routine, arg);
      my_task->timer = ORIGIN_OF_TIME;
      __po_hi_posix_initialize_task (my_task);
#elif defined (RTEMS_PURE)
      my_task->rtems_id = __po_hi_rtems_create_thread
        (priority, stack_size, core_id, start_routine, arg);
#elif defined (_WIN32)
      my_task->tid = __po_hi_win32_create_thread
        (id, priority, stack_size, start_routine, arg);
#elif defined (XENO_NATIVE)
      my_task->xeno_id = __po_hi_xenomai_create_thread
        (priority, stack_size, start_routine, arg);
#elif defined (SIMULATOR)
      my_task->um_id = um_thread_create (start_routine, stack_size, priority);
#else
      return (__PO_HI_UNAVAILABLE);
#endif
      nb_tasks++;
    }

  return (__PO_HI_SUCCESS);
}


int __po_hi_create_periodic_task (const __po_hi_task_id     id,
                                  const __po_hi_time_t*     period,
                                  const __po_hi_priority_t  priority,
                                  const __po_hi_stack_t     stack_size,
                                  const __po_hi_int8_t      core_id,
                                  void*                     (*start_routine)(void))
{
  /*
   * Send Task type to trace manager, if there is monitoring.
   */

#if defined (MONITORING)
   periodic_task_creation(id);
#endif

  if (__po_hi_create_generic_task( id, period , priority , stack_size, core_id, start_routine, NULL) != 1)
   {
      __DEBUGMSG ("ERROR when creating generic task (task id=%d)\n", id);
      return (__PO_HI_ERROR_CREATE_TASK);
   }

  /*
   * Compute the next period of the task, using the
   *__po_hi_time* functions.
   */
#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)

  // XXX The following is (a priori) not necessary, it should be
  // reviewed for all runtimes: the body of a periodic task already
  // call __po_hi_compute_next_period() as part of its skeleton

  /*if (__po_hi_compute_next_period (id) != __PO_HI_SUCCESS)
    {
      return (__PO_HI_ERROR_CLOCK);
    }
  */

#elif defined (XENO_NATIVE)
   int ret;

   ret = rt_task_set_periodic (&(tasks[id].xeno_id), TM_NOW,  (tasks[id].period.sec * 1000000000) + tasks[id].period.nsec);
   if (ret != 0)
   {
      __DEBUGMSG ("ERROR when calling rt_task_set_periodic on task %d, ret=%d\n", id, ret);
      return (__PO_HI_ERROR_CLOCK);
   }

   if (rt_task_start (&(tasks[id].xeno_id), (void*)start_routine, NULL))
   {
      __DEBUGMSG ("ERROR when starting the task\n");
   }
#endif
   tasks[id].task_category = TASK_PERIODIC;
   return (__PO_HI_SUCCESS);
}

void __po_hi_task_wait_offset (const __po_hi_time_t* time)
{

  if (time->sec == 0 && time->nsec == 0)
    return; // No need to wait, exit immediately

  tasks[__po_hi_get_task_id()].offset = *time;
}

int __po_hi_create_sporadic_task (const __po_hi_task_id     id,
                                  const __po_hi_time_t*     period,
                                  const __po_hi_priority_t  priority,
                                  const __po_hi_stack_t     stack_size,
                                  const __po_hi_int8_t      core_id,
                                  void*                     (*start_routine)(void) )
{
  /*
   * Send Task type to trace manager, if there is monitoring.
   */
#if defined (MONITORING)
   sporadic_task_creation(id);
#endif

  /*
   * Create generic task which will execute the routine given in the
   * last parameter. Typically, a sporadic thread will wait on a
   * mutex.
   */
  if (__po_hi_create_generic_task( id, period , priority , stack_size, core_id, start_routine, NULL) != 1)
    {
      return (__PO_HI_ERROR_CREATE_TASK);
    }

#if defined (XENO_NATIVE)
   int ret;

   ret = rt_task_set_periodic (&(tasks[id].xeno_id), TM_NOW,  tasks[id].period.sec * 1000000000 + tasks[id].period.nsec);
   if (ret != 0)
   {
      __DEBUGMSG ("ERROR when calling rt_task_set_periodic on task %d, ret=%d\n", id, ret);
      return (__PO_HI_ERROR_CLOCK);
   }

   if (rt_task_start (&(tasks[id].xeno_id), (void*)start_routine, NULL))
   {
      __DEBUGMSG ("ERROR when starting the task\n");
   }
#endif
   tasks[id].task_category = TASK_SPORADIC;
   return (__PO_HI_SUCCESS);
}

int __po_hi_task_delay_until (__po_hi_time_t* time, __po_hi_task_id task)
{
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
  struct timespec timer;
  int ret;

  timer.tv_sec = time->sec;

  timer.tv_nsec = time->nsec;

  pthread_mutex_lock (&tasks[task].mutex);

  ret = pthread_cond_timedwait (&tasks[task].cond, &tasks[task].mutex, &timer);

  if ( (ret != 0) && (ret != ETIMEDOUT))
    {
      ret = __PO_HI_ERROR_PTHREAD_COND;
    }
  else
    {
      ret = __PO_HI_SUCCESS;
    }

  pthread_mutex_unlock (&tasks[task].mutex);

  return (ret);
#elif defined (_WIN32)
   HANDLE hTimer = NULL;
   LARGE_INTEGER ularge;

   hTimer = CreateWaitableTimer(NULL, TRUE, NULL);
   ularge = __po_hi_unix_seconds_to_windows_tick (time->sec, time->nsec);

    if (!SetWaitableTimer(hTimer, &ularge, 0, NULL, NULL, 0))
    {
        __PO_HI_DEBUG_CRITICAL("[DELAY UNTIL] SetWaitableTimer failed (%d)\n", GetLastError());
        return 2;
    }

    if (WaitForSingleObject(hTimer, INFINITE) != WAIT_OBJECT_0)
    {
        __PO_HI_DEBUG_CRITICAL("[DELAY UNTIL] WaitForSingleObject failed (%d)\n", GetLastError());
    }

    if (CloseHandle(hTimer) != TRUE)
    {
        __PO_HI_DEBUG_CRITICAL("[DELAY UNTIL] CloseHandle failed (%d)\n", GetLastError());
    }


  return __PO_HI_SUCCESS;
#elif defined (XENO_NATIVE)
  int ret;
  ret =  rt_task_sleep_until (time->sec * 1000000000 + time->nsec);
  if (ret)
  {
      __DEBUGMSG ("[TASK] Error in rt_task_sleep_until, ret=%d\n", ret);
      return (__PO_HI_ERROR_PTHREAD_COND);
  }
  return (__PO_HI_SUCCESS);
#endif
  return (__PO_HI_UNAVAILABLE);
}

void __po_hi_tasks_killall ()
{
   int i;
   for (i = 0; i < __PO_HI_NB_TASKS; i++)
    {
       __DEBUGMSG ("Kill task %d\n", i);
#ifdef RTEMS_PURE
      rtems_task_delete (tasks[i].rtems_id);
#elif defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
      pthread_cancel (tasks[i].tid);
      __DEBUGMSG ("[TASKS] Cancel thread %p\n", tasks[i].tid);
#endif
    }
}

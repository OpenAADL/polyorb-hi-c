/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2011, European Space Agency (ESA).
 */

#if defined (RTEMS_POSIX) || defined (POSIX)
#include <pthread.h>
#include <sched.h>
#endif

#include <errno.h>
/* Headers from the executive */

#include <po_hi_config.h>
#include <po_hi_time.h>
#include <po_hi_task.h>
#include <po_hi_debug.h>
#include <po_hi_returns.h>
#include <po_hi_types.h>
/* Header files in PolyORB-HI */

#include <deployment.h>	

/* Header files from generated code */


int nb_tasks; /* number of created tasks */

typedef struct
{
  __po_hi_task_id     id;       /* Identifier of the task in the system */
  __po_hi_time_t      period;
#if defined(RTEMS_POSIX) || defined(POSIX)
  __po_hi_time_t      timer;
  pthread_t           tid;              /* The pthread_t type used by the
                                           POSIX library */
  pthread_mutex_t     mutex;
  pthread_cond_t      cond;
#elif defined(RTEMS_PURE)
  rtems_id            ratemon_period;
  rtems_id            rtems_id;
#elif defined(XENO_NATIVE)
  RT_TASK             xeno_id;
#endif
} __po_hi_task_t;
/*
 * Structure of a task, contains platform-dependent members
 */

__po_hi_task_t tasks[__PO_HI_NB_TASKS];
/* Array which contains all tasks informations */

void __po_hi_wait_for_tasks ()
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

#if defined(RTEMS_POSIX) || defined(POSIX)
  int i;

  for (i = 0; i < __PO_HI_NB_TASKS; i++)
    {
      pthread_join( tasks[i].tid , NULL );
    }
#endif
#ifdef RTEMS_PURE
  rtems_task_suspend(RTEMS_SELF);
#endif
}

/*
 * compute next period for a task
 * The argument is the task-id
 * The task must be a periodic task
 */
int __po_hi_compute_next_period (__po_hi_task_id task)
{

#if defined(RTEMS_POSIX) || defined(POSIX)
  __po_hi_time_t mytime;

  if (__po_hi_get_time (&mytime) != __PO_HI_SUCCESS)
    {
      return (__PO_HI_ERROR_CLOCK);
    }
  tasks[task].timer = __po_hi_add_times( mytime, tasks[task].period );
  
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
#else
   return (__PO_HI_UNAVAILABLE);
#endif
}

int __po_hi_wait_for_next_period (__po_hi_task_id task)
{
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
  int ret;
  __po_hi_task_delay_until (tasks[task].timer, task);
  if ( (ret = __po_hi_compute_next_period (task)) != 1)
    {
      return (__PO_HI_ERROR_CLOCK);
    }

  return (__PO_HI_SUCCESS);
#elif defined (RTEMS_PURE)
   rtems_status_code ret;
/*   ret = rtems_rate_monotonic_period (&tasks[task].ratemon_period, (rtems_interval)tasks[task].period * ); */
   ret = rtems_rate_monotonic_period (tasks[task].ratemon_period, tasks[task].period / _TOD_Microseconds_per_tick); 

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
   if ( ! rt_task_wait_period (NULL))
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
     tasks[i].period = 0;
     tasks[i].id     = invalid_task_id; 
#ifdef RTEMS_PURE
      tasks[i].ratemon_period = RTEMS_INVALID_ID;
#endif
  }

  nb_tasks = 0;

  return (__PO_HI_SUCCESS);
}

/*
 * For each kind of system, we declare a generic function that
 * create a thread. For POSIX-compliant systems, the function
 * is called __po_hi_posix_create_thread
 */

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
pthread_t __po_hi_posix_create_thread (__po_hi_priority_t priority, 
                                       __po_hi_stack_t    stack_size,
				       void*              (*start_routine)(void))
{
  int                policy;
  pthread_t          tid;
  pthread_attr_t     attr;
  struct sched_param param;

  if (pthread_attr_init (&attr) != 0)
    {
      return ((pthread_t)__PO_HI_ERROR_PTHREAD_ATTR);
    }

#if defined (POSIX) or defined (XENO_POSIX)
  if (pthread_attr_setscope (&attr, PTHREAD_SCOPE_SYSTEM) != 0)
    {
      return ((pthread_t)__PO_HI_ERROR_PTHREAD_ATTR);
    }
  if (stack_size != 0)
    {
      if (pthread_attr_setstacksize (&attr, stack_size) != 0)
	{
	  return ((pthread_t)__PO_HI_ERROR_PTHREAD_ATTR);
      }
    }
#elif defined (RTEMS_POSIX)
  if (pthread_attr_setscope (&attr, PTHREAD_SCOPE_PROCESS) != 0)
  {
    return ((pthread_t)__PO_HI_ERROR_PTHREAD_ATTR);
  }
#endif

  if (pthread_create (&tid, &attr, (void* (*)(void*))start_routine, NULL) != 0)
    {
      return ((pthread_t)__PO_HI_ERROR_PTHREAD_CREATE);
    }

  policy = SCHED_RR;
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

  if (pthread_setschedparam (tid, policy, &param)!=0)
    {
#ifdef __PO_HI_DEBUG
      __DEBUGMSG("CANNOT SET PRIORITY FOR TASK %d\n" , nb_tasks );
      __DEBUGMSG("IF YOU ARE USING POSIX IMPLEMENTATION\n");
      __DEBUGMSG("BE SURE TO BE LOGGED AS ROOT\n");
#endif
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


#ifdef RTEMS_PURE
rtems_id __po_hi_rtems_create_thread (__po_hi_priority_t priority, 
                                      __po_hi_stack_t    stack_size,
                                      void*              (*start_routine)(void))
{
  rtems_id rid;
   if (rtems_task_create (rtems_build_name( 'T', 'A', nb_tasks, ' ' ), 1, RTEMS_MINIMUM_STACK_SIZE, RTEMS_DEFAULT_MODES, RTEMS_DEFAULT_ATTRIBUTES | RTEMS_FLOATING_POINT, &rid) != RTEMS_SUCCESSFUL)
   {
      __DEBUGMSG ("ERROR when creating the task\n");
      return __PO_HI_ERROR_CREATE_TASK;
   }

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
                                     void*              (*start_routine)(void))
{
   RT_TASK newtask;

   if (! rt_task_create (&newtask, NULL, stack_size, priority, 0))
   {
      __DEBUGMSG ("ERROR when creating the task\n");
   }
   if ( ! rt_task_start (&newtask, (void*)start_routine, NULL))
   {
      __DEBUGMSG ("ERROR when starting the task\n");
   }

   return newtask;
}
#endif





int __po_hi_create_generic_task (__po_hi_task_id    id, 
                                 __po_hi_time_t     period, 
                                 __po_hi_priority_t priority, 
                                 __po_hi_stack_t   stack_size,
                                 void*              (*start_routine)(void))
{
  __po_hi_task_t* my_task;
  if (id == -1) 
    {
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
      __po_hi_posix_create_thread (priority, stack_size, start_routine);
      return (__PO_HI_SUCCESS);
#elif defined (XENO_NATIVE)
      __po_hi_xenomai_create_thread (priority, stack_size, start_routine);
      return (__PO_HI_SUCCESS);
#elif defined (RTEMS_PURE)
      __po_hi_rtems_create_thread (priority, stack_size, start_routine);
      return (__PO_HI_SUCCESS);
#else
      return (__PO_HI_UNAVAILABLE);
#endif
    } 
  else
    {
      my_task         = &(tasks[id]);
      my_task->period = period;
      my_task->id     = id;
     
#if defined (POSIX) || defined (RTEMS_POSIX)
      my_task->tid    = __po_hi_posix_create_thread (priority, stack_size, start_routine);
      __po_hi_posix_initialize_task (my_task);
#elif defined (RTEMS_PURE)
      my_task->rtems_id = __po_hi_rtems_create_thread (priority, stack_size, start_routine);
#elif defined (XENO_NATIVE)
      my_task->xeno_id = __po_hi_xenomai_create_thread (priority, stack_size, start_routine);
#else
      return (__PO_HI_UNAVAILABLE);
#endif
      nb_tasks++;
    }

  return (__PO_HI_SUCCESS);
}

int __po_hi_create_periodic_task (__po_hi_task_id    id, 
				  __po_hi_time_t     period, 
				  __po_hi_priority_t priority, 
				  __po_hi_stack_t    stack_size,
				  void*              (*start_routine)(void))
{
  if (__po_hi_create_generic_task( id, period , priority , stack_size, start_routine ) != 1)
    {
      return (__PO_HI_ERROR_CREATE_TASK);
    }

  /*
   * Compute the next period of the task, using the 
   *__po_hi_time* functions.
   */
#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
  if (__po_hi_compute_next_period (id) != __PO_HI_SUCCESS)
    {
      return (__PO_HI_ERROR_CLOCK);
    }
#elif defined (XENO_NATIVE)
   if (! rt_task_set_periodic (&(tasks[id].xeno_id), TM_NOW, tasks[id].period * 1000000))
   {
      return (__PO_HI_ERROR_CLOCK);
   }
#endif
    
  return (__PO_HI_SUCCESS);
}

int __po_hi_create_sporadic_task (__po_hi_task_id    id,
				  __po_hi_time_t     period, 
				  __po_hi_priority_t priority, 
				  __po_hi_stack_t    stack_size,
				  void*              (*start_routine)(void) )
{
  /*
   * Create generic task which will execute the routine given in the
   * last parameter. Typically, a sporadic thread will wait on a
   * mutex.
   */
  if (__po_hi_create_generic_task( id, period , priority , stack_size, start_routine ) != 1)
    {
      return (__PO_HI_ERROR_CREATE_TASK);
    }
  
  return (__PO_HI_SUCCESS);
}

int __po_hi_task_delay_until (__po_hi_time_t time, __po_hi_task_id task)
{
#if defined (POSIX) || defined (RTEMS_POSIX)
  struct timespec timer;
  int ret;

  timer.tv_sec = time / 1000000;
  
  timer.tv_nsec = (time - (timer.tv_sec*1000000)) * 1000;

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
#endif
#if defined (POSIX) || defined (RTEMS_POSIX)
      pthread_cancel (tasks[i].tid);
      __DEBUGMSG ("[TASKS] Cancel thread %d\n", (int) tasks[i].tid);
#endif
    }
}

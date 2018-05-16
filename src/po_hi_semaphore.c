/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2017 ESA & ISAE.
 */



#include <po_hi_config.h>
#include <po_hi_returns.h>
#include <po_hi_debug.h>
#include <po_hi_task.h>
#include <po_hi_types.h>
#include <po_hi_utils.h>
#include <po_hi_semaphore.h>

#include <deployment.h>


//#ifndef __PO_HI_NB_PROTECTED
//#define __PO_HI_NB_PROTECTED 0
//#endif

#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
#define __USE_UNIX98 1
#include <pthread.h>

#endif

#ifdef XENO_NATIVE
#include <native/mutex.h>
#include <native/cond.h>
#endif

#ifdef __PO_HI_RTEMS_CLASSIC_API
#include <rtems.h>
#endif


//#if __PO_HI_NB_PROTECTED > 0
//#endif /* __PO_HI_NB_PROTECTED > 0 */

int __po_hi_sem_init(__po_hi_sem_t* sem, const __po_hi_sem_protocol_t protocol, const int priority);
{
#ifdef __PO_HI_RTEMS_CLASSIC_API
   static int nb_mutex = 0;
#endif

   if (sem == NULL)
   {
      return __PO_HI_INVALID;
   }

   sem->protocol = __PO_HI_MUTEX_REGULAR;
   sem->priority = 0;

#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)

   /** Attribute and mutex initialization with protocol */
   if (pthread_mutexattr_init (&sem->posix_mutexattr) != 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when initializing the mutex attribute \n");
   }

   switch (protocol)
   {
       case __PO_HI_MUTEX_PCP:
       case __PO_HI_MUTEX_IPCP:
         {
            if (pthread_mutexattr_setprotocol (&sem->posix_mutexattr, PTHREAD_PRIO_PROTECT) != 0)
            {
               __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error while changing mutex protocol\n");
            }

            if (priority == 0)
            {
               sem->priority = __PO_HI_MAX_PRIORITY - 1;
            }
            else
            {
               sem->priority = priority;
            }

            if (pthread_mutexattr_setprioceiling (&sem->posix_mutexattr, sem->priority) != 0)
            {
               __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error while changing mutex priority\n");
            }
            break;
         }

      case __PO_HI_PROTECTED_PIP:
         {
            if (pthread_mutexattr_setprotocol (&sem->posix_mutexattr, PTHREAD_PRIO_INHERIT) != 0)
            {
               __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error while changing mutex protocol\n");
            }
            break;
         }
     //case __PO_HI_PROTECTED_REGULAR:
     case __PO_HI_MUTEX_REGULAR:
     //case __PO_HI_PROTECTED_PCP:
     //case __PO_HI_PROTECTED_INVALID:
	break;
   }

   if (pthread_mutex_init (&sem->posix_mutex, &sem->posix_mutexattr) != 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error while creating mutex\n");
        return __PO_HI_ERROR_SEM_CREATE;
   }

   /** Attribute and condvar initialization */
   int pthread_condattr_init(pthread_condattr_t *attr);
   if (pthread_condattr_init(&sem->posix_condattr) != 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when initializing the cond_var attribute \n");
   }

   if (pthread_cond_init (&sem->posix_condvar, &sem->posix_condattr) != 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error while creating the cond_var\n");
        return __PO_HI_ERROR_SEM_CREATE;
   }

#endif
#if defined (XENO_NATIVE)
    if (rt_mutex_create (&mutex->xeno_mutex, NULL) != 0)
    {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error while creating mutex\n");
      return __PO_HI_ERROR_SEM_CREATE;
    }
    if (rt_cond_create (&mutex->xeno_condvar, NULL) != 0)
    {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error while creating cond_var\n");
      return __PO_HI_ERROR_SEM_CREATE;
    }
#endif
#ifdef __PO_HI_RTEMS_CLASSIC_API
	//COUNTING?
    if (rtems_semaphore_create (rtems_build_name ('S', 'E', 'M' , 'A' + (char) nb_mutex++), 1, RTEMS_COUNTING_SEMAPHORE, __PO_HI_DEFAULT_PRIORITY, &sem->rtems_sem) != RTEMS_SUCCESSFUL)
    {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Cannot create RTEMS counting semaphore\n");
      return __PO_HI_ERROR_PROTECTED_CREATE;
    }
#endif
#ifdef _WIN32
    /** Initializing conditional variable and critical section*/
    //Use InitializeCriticalSectionAndSpinCount function?
    //Error messages?

    InitializeCriticalSection(&sem->win32_criticalsection);
    InitializeConditionVariable (&sem->win32_condvar);
  
#endif
   return (__PO_HI_SUCCESS);
}


int __po_hi_sem_wait(__po_hi_sem_t* sem)
{
#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
   /** Locking the mutex */
   if (pthread_mutex_lock (&sem->posix_mutex) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to lock mutex\n");
      return __PO_HI_ERROR_SEM_WAIT;
   }
   /** Waiting on a condition and unlocking the mutex while doing so */
   if (pthread_cond_wait(&sem->posix_condvar, &sem->posix_mutex) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to block the thread\n");
      return __PO_HI_ERROR_SEM_WAIT;
   }
#endif
#ifdef __PO_HI_RTEMS_CLASSIC_API
   if (rtems_semaphore_obtain (sem->rtems_sem, RTEMS_WAIT, RTEMS_NO_TIMEOUT) != RTEMS_SUCCESSFUL)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to obtain the rtems_sem\n");
      return __PO_HI_ERROR_SEM_WAIT;
   }
#endif
#ifdef XENO_NATIVE
   /** Locking the mutex */
   if (rt_mutex_acquire (&sem->xeno_mutex, TM_INFINITE) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to acquire/lock mutex\n");
      return __PO_HI_ERROR_SEM_WAIT;
   }
   /** Waiting on a condition and unlocking the mutex while doing so */
   if (rt_cond_wait (&sem->xeno_condvar, TM_INFINITE) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to block the task\n");
      return __PO_HI_ERROR_SEM_WAIT;
   }
#endif
#ifdef _WIN32
   /** Waiting for ownership of the specified critical section object */
   EnterCriticalSection(&sem->win32_criticalsection);
   /** Sleeps on the condition variable and releases the critical section */
   if (SleepConditionVariableCS(&sem->win32_condvar, &sem->win32_criticalsection, INFINITE) == 0)
   {
     __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Sleeping failed \n");
     return __PO_HI_ERROR_SEM_WAIT;
   }

#endif
   return __PO_HI_SUCCESS;
}


int __po_hi_sem_release(__po_hi_sem_t* sem)
{
#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
  
   /** Unblocking a thread */
   if (pthread_cond_signal(&sem->posix_condvar) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to unblock the thread\n");
      return __PO_HI_ERROR_SEM_RELEASE;
   }

   /** Unlocking the mutex */
   if (pthread_mutex_unlock (&sem->posix_mutex) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to unlock mutex\n");
      return __PO_HI_ERROR_SEM_RELEASE;
   }
#endif
#ifdef __PO_HI_RTEMS_CLASSIC_API
   if (rtems_semaphore_release (sem->rtems_sem) != RTEMS_SUCCESSFUL)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to release the rtems_sem\n");
      return __PO_HI_ERROR_SEM_RELEASE;
   }
#endif
#ifdef XENO_NATIVE
   
   /** Waiting on a condition and unlocking the mutex while doing so */
   if (rt_cond_signal (&sem->xeno_condvar) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to unblock the task\n");
      return __PO_HI_ERROR_SEM_RELEASE;
   }

   /** Unlocking the mutex */
   if (rt_mutex_release (&sem->xeno_mutex) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to unlock mutex\n");
      return __PO_HI_ERROR_SEM_RELEASE;
   }
#endif
#ifdef _WIN32
   //Before or after the exitCriticalSection ?
   /** Sleeps on the condition variable and releases the critical section */
   WakeConditionVariable(&sem->win32_condvar);

   /** Waiting for ownership of the specified critical section object */
   LeaveCriticalSection(&sem->win32_criticalsection);

#endif
  return __PO_HI_SUCCESS;
}


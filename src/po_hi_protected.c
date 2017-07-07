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
#include <po_hi_protected.h>

#include <deployment.h>

#ifndef __PO_HI_NB_PROTECTED
#define __PO_HI_NB_PROTECTED 0
#endif

#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
#define __USE_UNIX98 1
#include <pthread.h>
#endif

#ifdef XENO_NATIVE
#include <native/mutex.h>
#endif

#ifdef RTEMS_PURE
#include <rtems.h>
#endif

#if __PO_HI_NB_PROTECTED > 0

/* Declare only needed mutexes according to the generated
 * declarations. The __PO_HI_NB_PROTECTED is a generated macro that
 * represents the needed number of mutexes in the system.
 */

__po_hi_mutex_t                        __po_hi_protected_mutexes[__PO_HI_NB_PROTECTED];
extern __po_hi_protected_protocol_t    __po_hi_protected_configuration[__PO_HI_NB_PROTECTED];
extern __po_hi_uint8_t                 __po_hi_protected_priorities[__PO_HI_NB_PROTECTED];

int __po_hi_protected_init ()
{
   __po_hi_uint8_t i;

   for (i = 0 ; i < __PO_HI_NB_PROTECTED ; i++ )
   {
      if (__po_hi_mutex_init (&__po_hi_protected_mutexes[i], __po_hi_protected_configuration[i], __po_hi_protected_priorities[i]) != __PO_HI_SUCCESS)
      {
         __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when initialize protected resource %d\n", i);
      }
   }
   return (__PO_HI_SUCCESS);
}

int __po_hi_protected_lock (__po_hi_protected_t protected_id)
{
   __PO_HI_INSTRUMENTATION_VCD_WRITE("1w%d\n", protected_id);
   if (__po_hi_mutex_lock (&__po_hi_protected_mutexes[protected_id]) != __PO_HI_SUCCESS )
   {
      __PO_HI_INSTRUMENTATION_VCD_WRITE("0w%d\n", protected_id);
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when lock protected resource %d\n", protected_id);
      return __PO_HI_ERROR_PROTECTED_LOCK;
   }
   __PO_HI_INSTRUMENTATION_VCD_WRITE("0w%d\n", protected_id);
   __PO_HI_INSTRUMENTATION_VCD_WRITE("1l%d\n", protected_id);

   return __PO_HI_SUCCESS;
}

int __po_hi_protected_unlock (__po_hi_protected_t protected_id)
{

   __PO_HI_INSTRUMENTATION_VCD_WRITE("0l%d\n", protected_id);
  if (__po_hi_mutex_unlock (&__po_hi_protected_mutexes[protected_id]) != __PO_HI_SUCCESS )
    {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when unlock protected resource %d\n", protected_id);
      return __PO_HI_ERROR_PROTECTED_UNLOCK;
    }

  return __PO_HI_SUCCESS;
}

#endif /* __PO_HI_NB_PROTECTED > 0 */


int __po_hi_mutex_init (__po_hi_mutex_t* mutex, const __po_hi_mutex_protocol_t protocol, const int priority)
{
#ifdef RTEMS_PURE
   static int nb_mutex = 0;
#endif

   if (mutex == NULL)
   {
      return __PO_HI_INVALID;
   }

   mutex->protocol = __PO_HI_MUTEX_REGULAR;
   mutex->priority = 0;

#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
   if (pthread_mutexattr_init (&mutex->posix_mutexattr) != 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when initializing the mutex\n");
   }

   switch (protocol)
   {
       case __PO_HI_MUTEX_PCP:
       case __PO_HI_MUTEX_IPCP:
         {
            if (pthread_mutexattr_setprotocol (&mutex->posix_mutexattr, PTHREAD_PRIO_PROTECT) != 0)
            {
               __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error while changing mutex protocol\n");
            }

            if (priority == 0)
            {
               mutex->priority = __PO_HI_MAX_PRIORITY - 1;
            }
            else
            {
               mutex->priority = priority;
            }

            if (pthread_mutexattr_setprioceiling (&mutex->posix_mutexattr, mutex->priority) != 0)
            {
               __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error while changing mutex priority\n");
            }
            break;
         }

      case __PO_HI_PROTECTED_PIP:
         {
            if (pthread_mutexattr_setprotocol (&mutex->posix_mutexattr, PTHREAD_PRIO_INHERIT) != 0)
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

    if (pthread_mutex_init (&mutex->posix_mutex, &mutex->posix_mutexattr) != 0)
    {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error while creating mutex\n");
        return __PO_HI_ERROR_UNKNOWN;
     }
#endif
#if defined (XENO_NATIVE)
    if (rt_mutex_create (&mutex->xeno_mutex, NULL) != 0)
    {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error while creating mutex\n");
      return __PO_HI_ERROR_UNKNOWN;
    }
#endif
#ifdef RTEMS_PURE
    if (rtems_semaphore_create (rtems_build_name ('P', 'S', 'E' , 'A' + (char) nb_mutex++), 1, RTEMS_BINARY_SEMAPHORE, __PO_HI_DEFAULT_PRIORITY, &mutex->rtems_mutex) != RTEMS_SUCCESSFUL)
    {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Cannot create RTEMS binary semaphore\n");
      return __PO_HI_ERROR_PROTECTED_CREATE;
    }
#endif
#ifdef _WIN32
    mutex->win32_mutex = CreateMutex (NULL, FALSE, NULL);
    if (mutex->win32_mutex == NULL)
    {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Cannot create WIN32 mutex\n");
      return __PO_HI_ERROR_PROTECTED_CREATE;
    }
#endif
   return (__PO_HI_SUCCESS);
}

int __po_hi_mutex_lock (__po_hi_mutex_t* mutex)
{

#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
   if (pthread_mutex_lock (&mutex->posix_mutex) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to lock mutex\n");
      return __PO_HI_ERROR_MUTEX_LOCK;
   }
#endif
#ifdef RTEMS_PURE
   if (rtems_semaphore_obtain (mutex->rtems_mutex, RTEMS_WAIT, RTEMS_NO_TIMEOUT) != RTEMS_SUCCESSFUL)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to lock mutex\n");
      return __PO_HI_ERROR_MUTEX_LOCK;
   }
#endif
#ifdef XENO_NATIVE
   if (rt_mutex_acquire (&mutex->xeno_mutex, TM_INFINITE) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to lock mutex\n");
      return __PO_HI_ERROR_MUTEX_LOCK;
   }
#endif
#ifdef _WIN32
   DWORD status;
   status = WaitForSingleObject( mutex->win32_mutex, INFINITE);

   if (status == WAIT_ABANDONED)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Lock failed (abandon)\n");
      return __PO_HI_ERROR_MUTEX_LOCK;
   }
   if (status == WAIT_FAILED)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Lock failed (failure)\n");
      return __PO_HI_ERROR_MUTEX_LOCK;
   }

#endif
   return __PO_HI_SUCCESS;
}

int __po_hi_mutex_unlock (__po_hi_mutex_t* mutex)
{
#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
  if (pthread_mutex_unlock (&mutex->posix_mutex) != 0 )
    {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to unlock mutex\n");
      return __PO_HI_ERROR_MUTEX_UNLOCK;
    }
#endif
#ifdef RTEMS_PURE
   if (rtems_semaphore_release (mutex->rtems_mutex) != RTEMS_SUCCESSFUL)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to unlock mutex\n");
      return __PO_HI_ERROR_MUTEX_UNLOCK;
   }
#endif
#ifdef XENO_NATIVE
  if (rt_mutex_release (&mutex->xeno_mutex) != 0 )
    {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Error when trying to unlock mutex\n");
      return __PO_HI_ERROR_MUTEX_UNLOCK;
    }
#endif
#ifdef _WIN32
   if (ReleaseMutex (mutex->win32_mutex) == 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[PROTECTED] Release failed\n");
      return __PO_HI_ERROR_MUTEX_UNLOCK;
   }
#endif
  return __PO_HI_SUCCESS;
}

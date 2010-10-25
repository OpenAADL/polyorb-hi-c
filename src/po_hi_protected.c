/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#include <po_hi_config.h>
#include <po_hi_protected.h>
#include <po_hi_returns.h>
#include <po_hi_debug.h>
#include <po_hi_task.h>
#include <po_hi_types.h>
#include <deployment.h>

#ifndef __PO_HI_NB_PROTECTED
#define __PO_HI_NB_PROTECTED 0
#endif

#if __PO_HI_NB_PROTECTED > 0

#if defined (RTEMS_POSIX) || defined (POSIX)
#define __USE_UNIX98 1
#include <pthread.h>

/* Declare only needed mutexes according to the generated
 * declarations. The __PO_HI_NB_PROTECTED is a generated macro that
 * represents the needed number of mutexes in the system.
 */

pthread_mutex_t                        __po_hi_protected_mutexes[__PO_HI_NB_PROTECTED];
pthread_mutexattr_t                    __po_hi_protected_mutexes_attr[__PO_HI_NB_PROTECTED];
extern __po_hi_protected_protocol_t    __po_hi_protected_configuration[__PO_HI_NB_PROTECTED];
extern __po_hi_uint8_t                 __po_hi_protected_priorities[__PO_HI_NB_PROTECTED];

int __po_hi_protected_init ()
{
   __po_hi_uint8_t i;
   __po_hi_uint8_t prio;

   for (i = 0 ; i < __PO_HI_NB_PROTECTED ; i++ )
   {
      if (pthread_mutexattr_init (&__po_hi_protected_mutexes_attr[i]) != 0)
      {
         __PO_HI_DEBUG_DEBUG ("[PROTECTED] Error while initializing mutex attr\n");
      }

      if (__po_hi_protected_configuration[i] == __PO_HI_PROTECTED_IPCP)
      {
         if (pthread_mutexattr_setprotocol (&__po_hi_protected_mutexes_attr[i], PTHREAD_PRIO_PROTECT) != 0)
         {
            __PO_HI_DEBUG_DEBUG ("[PROTECTED] Error while changing mutex protocol\n");
         }

         prio = __po_hi_protected_priorities[i];

         if (prio == 0)
         {
#include <po_hi_task.h>
            prio = __PO_HI_MAX_PRIORITY - 1;
         }

         if (pthread_mutexattr_setprioceiling (&__po_hi_protected_mutexes_attr[i], prio) != 0)
         {
            __PO_HI_DEBUG_DEBUG ("[PROTECTED] Error while changing mutex priority\n");
         }

      }

      if (__po_hi_protected_configuration[i] == __PO_HI_PROTECTED_PIP)
      {
         if (pthread_mutexattr_setprotocol (&__po_hi_protected_mutexes_attr[i], PTHREAD_PRIO_INHERIT) != 0)
         {
            __PO_HI_DEBUG_DEBUG ("[PROTECTED] Error while changing mutex protocol\n");
         }
      }

      if (pthread_mutex_init (&__po_hi_protected_mutexes[i], &__po_hi_protected_mutexes_attr[i]) != 0)
      {
         __PO_HI_DEBUG_DEBUG ("[PROTECTED] Error while creating mutex %d\n", i);
         return __PO_HI_ERROR_PROTECTED_CREATE;
      }

      __PO_HI_DEBUG_DEBUG ("[PROTECTED] Successfully create mutex %d\n", i);
   }
   return (__PO_HI_SUCCESS);
}

int __po_hi_protected_lock (__po_hi_protected_t protected_id)
{
   if (pthread_mutex_lock (&__po_hi_protected_mutexes[protected_id]) != 0 )
   {
      return __PO_HI_ERROR_PROTECTED_LOCK;
   }
   return __PO_HI_SUCCESS;
}

int __po_hi_protected_unlock (__po_hi_protected_t protected_id)
{
  if (pthread_mutex_unlock (&__po_hi_protected_mutexes[protected_id]) != 0 )
    {
      return __PO_HI_ERROR_PROTECTED_UNLOCK;
    }
  return __PO_HI_SUCCESS;
}
#endif /* POSIX or RTEMS_POSIX */


#if defined (RTEMS_PURE)

/* Declare only needed mutexes according to the generated
 * declarations. The __PO_HI_NB_PROTECTED is a generated macro that
 * represents the needed number of mutexes in the system.
 */

#include <rtems.h>

rtems_id __po_hi_protected_mutexes[__PO_HI_NB_PROTECTED];

int __po_hi_protected_init ()
{
   __po_hi_uint8_t      i;
   rtems_status_code    ret;

   for (i = 0 ; i < __PO_HI_NB_PROTECTED ; i++ )
   {
      /*FIXME : handle different locking protocols !!! */
      ret = rtems_semaphore_create (rtems_build_name ('P', 'S', 'E' , 'A' + (char) i), 1, RTEMS_BINARY_SEMAPHORE, __PO_HI_DEFAULT_PRIORITY, &(__po_hi_protected_mutexes[i]));
      if (ret != RTEMS_SUCCESSFUL)
      {
         __DEBUGMSG ("[PROTECTED] Cannot create binary semaphore, error code=%d\n", ret);
         return __PO_HI_ERROR_PROTECTED_CREATE;
      }
   }
   return (__PO_HI_SUCCESS);
}

int __po_hi_protected_lock (__po_hi_protected_t protected_id)
{
   rtems_status_code ret;
   __DEBUGMSG ("[PROTECTED] Try to obtain binary semaphore for protected object %d\n", protected_id);
   ret = rtems_semaphore_obtain (__po_hi_protected_mutexes[protected_id], RTEMS_WAIT, RTEMS_NO_TIMEOUT);
   if (ret != RTEMS_SUCCESSFUL)
   {
      __DEBUGMSG ("[PROTECTED] Cannot obtain binary semaphore in __po_hi_protected_lock()\n");
      return __PO_HI_ERROR_PROTECTED_LOCK;
   }

   return __PO_HI_SUCCESS;
}

int __po_hi_protected_unlock (__po_hi_protected_t protected_id)
{
   rtems_status_code ret;
   __DEBUGMSG ("[PROTECTED] Try to release protected object %d\n", protected_id);
   ret = rtems_semaphore_release (__po_hi_protected_mutexes[protected_id]);
   if (ret != RTEMS_SUCCESSFUL)
   {
      __DEBUGMSG ("[PROTECTED] Cannot release semaphore in __po_hi_protected_unlock()\n");
      return __PO_HI_ERROR_PROTECTED_UNLOCK;
   }

  return __PO_HI_SUCCESS;
}
#endif /* POSIX or RTEMS_POSIX */


#endif /* __PO_HI_NB_PROTECTED > 0 */

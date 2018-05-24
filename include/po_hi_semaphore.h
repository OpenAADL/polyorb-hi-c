/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2014 ESA & ISAE.
 */

#ifndef __PO_HI_SEMAPHORE_H__
#define __PO_HI_SEMAPHORE_H__

#include <po_hi_protected.h>
#include <stdint.h>
#include <deployment.h>
#include <po_hi_gqueue.h>

//#define __PO_HI_PROTECTED_TYPE_REGULAR    0
//#define __PO_HI_PROTECTED_TYPE_PIP        1
//#define __PO_HI_PROTECTED_TYPE_PCP        2

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   #include <stdlib.h>
   #include <stdint.h>
   #include <time.h>
   #include <pthread.h>
   #include <semaphore.h>
//   #include <sys/sem.h>
#endif

#if defined (__PO_HI_RTEMS_CLASSIC_API)
   #include <rtems.h>
#endif

#if defined (XENO_NATIVE)
   #include <native/mutex.h>
#endif

#ifdef _WIN32
#include <windows.h>
#endif

/** Structure defining a semaphore */
typedef struct
{    
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   __po_hi_mutex_t      mutex;
   pthread_cond_t       posix_condvar;
   pthread_condattr_t   posix_condattr;
#endif
#if defined (__PO_HI_RTEMS_CLASSIC_API)
   rtems_id             rtems_sem;
   rtems_id		rtems_barrier;
#endif
#if defined (XENO_NATIVE)
   __po_hi_mutex_t      mutex;
   RT_COND              xeno_condvar;
#endif
#if defined (_WIN32)
   HANDLE               win32_event;
   CRITICAL_SECTION     win32_criticalsection;
#endif
}__po_hi_sem_t;


/** USED TO WORK ON SEMAPHORES */

/** A semaphore sem is initialized.
 * The protocol and priority attributes are used by the API mutex.
 * The attribute nb is the identifier of the task, used to name
 * the rtems semaphore.
 * 
 * Returns __PO_HI_SUCCESS if successful.
 * Can return __PO_HI_ERROR_SEM_CREATE if there is an error.
*/

int __po_hi_sem_init(__po_hi_sem_t* sem, const __po_hi_mutex_protocol_t protocol, const int priority, int nb);

/** Only The condition variables of a semaphore are told to wait.
 * To ensure the protection, the po_hi_sem_mutex_wait must be used before !
 * The lock must has been taken already (tested in POSIX by a trylock).
 * This function is used when make a sem_wait is separated in two steps : 
   * Locking the mutex (role of po_hi_sem_mutex_wait).
   * Make a test and then making a condvar_wait (role of po_hi_sem_wait).
 * 
 * Returns __PO_HI_SUCCESS if successful.
 * Can return __PO_HI_ERROR_SEM_WAIT if there is an error.
*/
int __po_hi_sem_wait(__po_hi_sem_t* sem);

/** The mutex attribute of a semaphore is locked.
 * This function is used when make a sem_wait is separated in two steps : 
   * Locking the mutex (role of po_hi_sem_mutex_wait).
   * Make a test and then making a condvar_wait (role of po_hi_sem_wait).
 * 
 * This function is also used when only a mutex is needed in the gqueue.
 * Returns __PO_HI_SUCCESS if successful.
 * Can return __PO_HI_ERROR_SEM_WAIT if there is an error.
*/
int __po_hi_sem_mutex_wait(__po_hi_sem_t* sem);

/** The semaphore is COMPLETELY RELEASED. (both condvar and mutex).
 * Returns __PO_HI_SUCCESS if successful.
 * Can return __PO_HI_ERROR_SEM_RELEASE if there is an error.
*/
int __po_hi_sem_release(__po_hi_sem_t* sem);

/** The mutex attribute of a semaphore is released.
 * This function is used when you don't want to do a condvar_signal, and
 * want to let it stay on a wait mode.
 * This function is also used when only a mutex is needed in the gqueue.
 * Returns __PO_HI_SUCCESS if successful.
 * Can return __PO_HI_ERROR_SEM_RELEASE if there is an error.
*/
int __po_hi_sem_mutex_release(__po_hi_sem_t* sem);


/** USED TO FILL THE SEMAPHORE GQUEUE ARRAY 
 * Only those functions are used directly in the gqueue 
 * Their result will be tested in the gqueue with an assert */

/** Used to do the po_hi_sem_init function on a semaphore contained in the semaphore array 
 * Returns the result of that function applied to the specified semaphore.
 * Returns __PO_HI_SUCCESS if successful.
*/
int __po_hi_sem_init_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);

/** Used to do the po_hi_sem_wait function on a semaphore contained in the semaphore array 
 * Returns the result of that function applied to the specified semaphore.
 * Returns __PO_HI_SUCCESS if successful.
*/
int __po_hi_sem_wait_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);

/** Used to do the po_hi_sem_mutex_wait function on a semaphore contained in the semaphore array 
 * Returns the result of that function applied to the specified semaphore.
 * Returns __PO_HI_SUCCESS if successful.
*/
int __po_hi_sem_mutex_wait_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);

/** Used to do the po_hi_sem_release function on a semaphore contained in the semaphore array 
 * Returns the result of that function applied to the specified semaphore.
 * Returns __PO_HI_SUCCESS if successful.
*/
int __po_hi_sem_release_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);

/** Used to do the po_hi_sem_mutex_release function on a semaphore contained in the semaphore array 
 * Returns the result of that function applied to the specified semaphore.
 * Returns __PO_HI_SUCCESS if successful.
*/
int __po_hi_sem_mutex_release_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);





#endif /*  __PO_HI_SEMAPHORE_H__ */

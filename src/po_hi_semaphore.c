/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2018 ESA & ISAE.
 */

#include <po_hi_returns.h>
#include <po_hi_config.h>

#include <po_hi_debug.h>
#include <po_hi_task.h>
#include <po_hi_types.h>
#include <po_hi_utils.h>
#include <po_hi_semaphore.h>

#include <deployment.h>
#include <assert.h>

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

/* TO INITIALIZE THE STRUCTURES */
int __po_hi_sem_init(__po_hi_sem_t* sem, const __po_hi_mutex_protocol_t protocol, const int priority, int id)
{
   __PO_HI_DEBUG_INFO ("[SEM] Sem Task %d is initialized", id);

#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
   /* Attribute and mutex initialization */
   if (__po_hi_mutex_init (&sem->mutex, protocol, priority) != __PO_HI_SUCCESS)
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when initializing the mutex \n");
      return __PO_HI_ERROR_SEM_CREATE;
   }

   /* Attribute and condvar initialization */
   if (pthread_condattr_init(&sem->posix_condattr) != 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when initializing the cond_var attribute \n");
      /* No return here, such as in the protected API for the mutex attribute */
   }
   if (pthread_cond_init (&sem->posix_condvar, &sem->posix_condattr) != 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error while creating the cond_var\n");
      return __PO_HI_ERROR_SEM_CREATE;
   }

#elif defined (XENO_NATIVE)
    /* Mutex initialization */
    /* The protocol and priority are unused here */
    int ret = __po_hi_mutex_init (&sem->mutex, __PO_HI_MUTEX_REGULAR, 0);
    if (ret != __PO_HI_SUCCESS)
    {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when initializing the mutex, code = %d \n, ret");
      return __PO_HI_ERROR_SEM_CREATE;
    }
    /* Conditional Variable initialization */
    ret = rt_cond_create (&mutex->xeno_condvar, NULL);
    if (ret != 0)
    {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error while creating cond_var, code = %d \n, ret");
      return __PO_HI_ERROR_SEM_CREATE;
    }

#elif defined (__PO_HI_RTEMS_CLASSIC_API)
    /* RTEMS Semaphore initialization */
    rtems_status_code code = rtems_semaphore_create (rtems_build_name ('G', 'S', 'E' , 'A' + (char) id), 1, RTEMS_BINARY_SEMAPHORE, __PO_HI_DEFAULT_PRIORITY, &sem->rtems_sem);
    if (code != RTEMS_SUCCESSFUL)
    {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Cannot create semaphore of task %d, error code=%d\n", id, code);
      return __PO_HI_ERROR_SEM_CREATE;
    }
    /* Barrier initialization */
    code = rtems_barrier_create (rtems_build_name ('G', 'S', 'I' , 'A' + (char) id),RTEMS_BARRIER_AUTOMATIC_RELEASE , 10, &sem->rtems_barrier);
    if (code != RTEMS_SUCCESSFUL)
    {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Cannot create barrier of task %d, error code=%d\n", id, code);
      return __PO_HI_ERROR_SEM_CREATE;
    }

#elif defined (_WIN32)
    /* Initializing event and critical section*/
    sem->win32_event = CreateEvent (NULL, FALSE, FALSE, NULL);
    if (sem->win32_event == NULL)
    {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] CreateEvent failed (%d)\n", GetLastError());
      return __PO_HI_ERROR_SEM_CREATE;
    }
    InitializeCriticalSection(&sem->win32_criticalsection);

#else
#error Unsupported platform
#endif
   return (__PO_HI_SUCCESS);
}


/* TO LOCK/UNLOCK SEMAPHORES AND THEIR MUTEXES */
int __po_hi_sem_wait(__po_hi_sem_t* sem)
{
#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
   /* Locking the mutex */
   if (pthread_mutex_trylock(&sem->mutex.posix_mutex) == 0 ) {
     pthread_mutex_lock(&sem->mutex.posix_mutex);
   }
   
   /* Waiting on a condition and unlocking the mutex while doing so */
   if (pthread_cond_wait(&sem->posix_condvar, &sem->mutex.posix_mutex) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when trying to block the thread\n");
      return __PO_HI_ERROR_SEM_WAIT;
   }

#elif defined (__PO_HI_RTEMS_CLASSIC_API)
   if (rtems_semaphore_release (sem->rtems_sem) != RTEMS_SUCCESSFUL)
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when trying to release to next obtain the rtems_sem\n");
      return __PO_HI_ERROR_SEM_WAIT;
   }
   rtems_task_wake_after (1);
   //rtems_task_wake_after( RTEMS_YIELD_PROCESSOR );
   if (rtems_semaphore_obtain (sem->rtems_sem, RTEMS_WAIT, RTEMS_NO_TIMEOUT) != RTEMS_SUCCESSFUL)
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when trying to obtain the rtems_sem\n");
      return __PO_HI_ERROR_SEM_WAIT;
   }

#elif defined (XENO_NATIVE)
   /* Locking the mutex */
   //if (__po_hi_mutex_lock(&sem->mutex) != __PO_HI_SUCCESS )
   //{
   //   __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when trying to acquire/lock mutex\n");
   //   return __PO_HI_ERROR_SEM_WAIT;
   //}
   /* Waiting on a condition and unlocking the mutex while doing so */
   if (rt_cond_wait (&sem->xeno_condvar, TM_INFINITE) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when trying to block the task\n");
      return __PO_HI_ERROR_SEM_WAIT;
   }

#elif defined (_WIN32)
  /* Letting go of the ownership to wait for it later */
  LeaveCriticalSection(&sem->win32_criticalsection);
  /* Event object */
  int ret = WaitForSingleObject (&sem->win32_event,INFINITE);
  if (ret == WAIT_FAILED)
  {
     __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Wait failed\n");
  }
  /* Waiting for ownership of the specified critical section object */
  EnterCriticalSection(&sem->win32_criticalsection);

#endif
  
   return __PO_HI_SUCCESS;
}

/* To work only on a mutex */
int __po_hi_sem_mutex_wait(__po_hi_sem_t* sem){

#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)|| defined (XENO_NATIVE)
  if (__po_hi_mutex_lock(&sem->mutex) != __PO_HI_SUCCESS )
  {
     __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE MUTEX] Error when trying to acquire/lock mutex\n");
     return __PO_HI_ERROR_SEM_WAIT;
  }

#elif defined (__PO_HI_RTEMS_CLASSIC_API)
  if (rtems_semaphore_obtain (sem->rtems_sem, RTEMS_WAIT, RTEMS_NO_TIMEOUT) != RTEMS_SUCCESSFUL)
   {
     __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE MUTEX] Error when trying to obtain the rtems_sem\n");
     return __PO_HI_ERROR_SEM_WAIT;
   }

#elif defined (_WIN32)
  EnterCriticalSection(&sem->win32_criticalsection);
#endif
  return __PO_HI_SUCCESS;
}

int __po_hi_sem_release(__po_hi_sem_t* sem)
{
#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)

   /* Unblocking a thread */
   if (pthread_cond_signal(&sem->posix_condvar) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when trying to unblock the thread\n");
      return __PO_HI_ERROR_SEM_RELEASE;
   }
   /* Unlocking the mutex */
   if (__po_hi_mutex_unlock(&sem->mutex) != __PO_HI_SUCCESS )
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when trying to unlock mutex\n");
      return __PO_HI_ERROR_SEM_RELEASE;
   }

#elif defined(__PO_HI_RTEMS_CLASSIC_API)
   if (rtems_semaphore_release (sem->rtems_sem) != RTEMS_SUCCESSFUL)
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when trying to release the rtems_sem\n");
      return __PO_HI_ERROR_SEM_RELEASE;
   }

#elif defined (XENO_NATIVE)
   /* Unblocking all tasks */
   if (rt_cond_broadcast (&sem->xeno_condvar) != 0 )
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when trying to unblock the task\n");
      return __PO_HI_ERROR_SEM_RELEASE;
   }
   /* Unlocking the mutex */
   if (__po_hi_mutex_unlock(&sem->x_mutex) != __PO_HI_SUCCESS )
   {
      __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE] Error when trying to unlock mutex\n");
      return __PO_HI_ERROR_SEM_RELEASE;
   }

#elif defined (_WIN32)
  /* Waiting for ownership of the specified critical section object */
  LeaveCriticalSection(&sem->win32_criticalsection);
  if (! SetEvent(&sem->win32_event)
  {
      __DEBUGMSG("SetEvent failed (%d)\n", GetLastError());
      return __PO_HI_ERROR_SEM_RELEASE;
  }
#endif
  return __PO_HI_SUCCESS;
}

/* To work only on a mutex */
int __po_hi_sem_mutex_release(__po_hi_sem_t* sem){
#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)|| defined (XENO_NATIVE)
  if (__po_hi_mutex_unlock(&sem->mutex) != __PO_HI_SUCCESS )
  {
     __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE MUTEX] Error when trying to unlock the mutex\n");
     return __PO_HI_ERROR_SEM_RELEASE;
  }
#elif defined (__PO_HI_RTEMS_CLASSIC_API)
if (rtems_semaphore_release (sem->rtems_sem) != RTEMS_SUCCESSFUL)
   {
     __PO_HI_DEBUG_CRITICAL ("[SEMAPHORE MUTEX] Error when trying to release the rtems_sem\n");
     return __PO_HI_ERROR_SEM_RELEASE;
   }

#elif defined (_WIN32)
  EnterCriticalSection(&sem->win32_criticalsection);
#endif
  return __PO_HI_SUCCESS;
}

/* TO INITIALIZE THE SEM_GQUEUE_ARRAY */
int __po_hi_sem_init_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id)
{
  int result = __po_hi_sem_init(&array[id], __PO_HI_MUTEX_REGULAR, 0, id);
  __DEBUGMSG("SEM_INIT task number : %d, result : %d\n", id, result);


#if defined (POSIX) || defined (XENO_POSIX)
   // XXX disabled for OS X
#ifndef __MACH__ // OS X bugs on this attribute
   if (pthread_mutexattr_setpshared(&array[id].mutex.posix_mutexattr,PTHREAD_PROCESS_SHARED) !=0){
     __DEBUGMSG("MACH, setpshared task : %d, result : %d\n", id, result);
     return __PO_HI_ERROR_PTHREAD_MUTEX;
   }
#endif
#endif

  return result;
}

/* TO ACCESS TO THE SEM_GQUEUE_ARRAY */
int __po_hi_sem_wait_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id)
{
  int result = __PO_HI_SUCCESS;
  result = __po_hi_sem_wait(&array[id]);
  __DEBUGMSG("SEM_WAIT_GQUEUE task number : %d, result : %d\n", id, result);
  return result;
}

int __po_hi_sem_mutex_wait_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id)
{
  int result = __PO_HI_SUCCESS;
  result = __po_hi_sem_mutex_wait(&array[id]);
  __DEBUGMSG("SEM_MUTEX_WAIT_GQUEUE task number : %d, result : %d\n", id, result);
  return result;

}

int __po_hi_sem_release_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id)
{
  int result = __PO_HI_SUCCESS;
  result = __po_hi_sem_release(&array[id]);
  __DEBUGMSG("SEM_RELEASE_GQUEUE task number : %d, result : %d\n", id, result);
  return result;
}

int __po_hi_sem_mutex_release_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id)
{
  int result = __PO_HI_SUCCESS;
  result = __po_hi_sem_mutex_release(&array[id]);
  __DEBUGMSG("SEM_MUTEX_RELEASE_GQUEUE task number : %d, result : %d\n", id, result);
  return result;
}

/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2018 ESA & ISAE.
 */

#ifndef __PO_HI_SEMAPHORE_H__
#define __PO_HI_SEMAPHORE_H__

#include <po_hi_protected.h>
#include <stdint.h>
#include <deployment.h>
#include <po_hi_gqueue.h>

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   #include <stdlib.h>
   #include <stdint.h>
   #include <time.h>
   #include <pthread.h>
   #include <semaphore.h>

#elif defined (__PO_HI_RTEMS_CLASSIC_API)
   #include <rtems.h>

#elif defined (XENO_NATIVE)
   #include <native/mutex.h>

#elif defined (_WIN32)
#include <windows.h>
#endif

/**
 * \struct __po_hi_sem_t.
 * \brief Structure defining a semaphore.
 */
typedef struct __po_hi_sem_t __po_hi_sem_t;
struct __po_hi_sem_t
{
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   __po_hi_mutex_t      mutex;
   pthread_cond_t       posix_condvar;
   pthread_condattr_t   posix_condattr;
#elif defined (__PO_HI_RTEMS_CLASSIC_API)
   rtems_id             rtems_sem;
   rtems_id		rtems_barrier;
#elif defined (XENO_NATIVE)
   __po_hi_mutex_t      mutex;
   RT_COND              xeno_condvar;
#elif defined (_WIN32)
   HANDLE               win32_event;
   CRITICAL_SECTION     win32_criticalsection;
#endif
};

/* USED TO WORK ON SEMAPHORES */

/**
 * \brief A semaphore sem is initialized.
 *
 * \param sem Semaphore structure to be initialized.
 * \param protocol Parameter used in the mutex initialization if there is one (Protected API).
 * \param priority Parameter used in the mutex initialization if there is one (Protected API).
 * \param nb Identifier of the task, used to name the synchronization object.
 * \return __PO_HI_SUCCESS if successful.
 * \return __PO_HI_ERROR_SEM_CREATE if there is an error.
 */
int __po_hi_sem_init(__po_hi_sem_t* sem, const __po_hi_mutex_protocol_t protocol, const int priority, int nb);


/**
 * \brief A wait is done only on the condition variables of a semaphore.
 *
 * To ensure the protection, the po_hi_sem_mutex_wait must be used before.
 * The lock must has been taken already (tested in POSIX by a trylock).
 * This function is used when make a sem_wait is separated in two steps.
 * First, Locking the mutex (role of po_hi_sem_mutex_wait).
 * Second, Make a test and then making a condvar_wait (role of po_hi_sem_wait).
 *
 * \param sem Semaphore structure to be worked on.
 * \return __PO_HI_SUCCESS if successful.
 * \return __PO_HI_ERROR_SEM_WAIT if there is an error.
 */
int __po_hi_sem_wait(__po_hi_sem_t* sem);

/**
 * \brief The mutex attribute of a semaphore is locked.
 *
 * This function is used when make a sem_wait is separated in two steps.
 * First, Locking the mutex (role of po_hi_sem_mutex_wait).
 * Second, Make a test and then making a condvar_wait (role of po_hi_sem_wait).
 *
 * This function is also used when only a mutex is needed in the gqueue.
 * \param sem Semaphore structure to be worked on.
 * \return __PO_HI_SUCCESS if successful.
 * \return __PO_HI_ERROR_SEM_WAIT if there is an error.
 */
int __po_hi_sem_mutex_wait(__po_hi_sem_t* sem);

/**
 * \brief The semaphore is released.
 * 
 * The semaphore is COMPLETELY RELEASED. (both condvar and mutex).
 * \param sem Semaphore structure to be worked on.
 * \return __PO_HI_SUCCESS if successful.
 * \return __PO_HI_ERROR_SEM_RELEASE if there is an error.
 */
int __po_hi_sem_release(__po_hi_sem_t* sem);

/**
 * \brief The mutex attribute of a semaphore is released.
 * 
 * This function is used when you don't want to do a condvar_signal, and
 * want to let it stay on a wait mode.
 * This function is also used when only a mutex is needed in the gqueue.
 * \param sem Semaphore structure to be worked on.
 * \return __PO_HI_SUCCESS if successful.
 * \return __PO_HI_ERROR_SEM_RELEASE if there is an error.
 */
int __po_hi_sem_mutex_release(__po_hi_sem_t* sem);


/* USED TO WORK ON THE GQUEUE SEM ARRAY */

/**
 * \brief Used to do the po_hi_sem_init function on a semaphore contained in the semaphore array.
 * 
 * \param array The array of semaphores used in the gqueue.
 * \param id Identifier of the task.
 * \return __PO_HI_SUCCESS if successful.
 * \return the result of that function applied to the specified semaphore if there is an error.
 */
int __po_hi_sem_init_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);

/**
 * \brief Used to do the po_hi_sem_wait function on a semaphore contained in the semaphore array.
 * 
 * \param array The array of semaphores used in the gqueue.
 * \param id Identifier of the task.
 * \return __PO_HI_SUCCESS if successful.
 * \return the result of that function applied to the specified semaphore if there is an error.
 */
int __po_hi_sem_wait_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);

/**
 * \brief Used to do the po_hi_sem_mutex_wait function on a semaphore contained in the semaphore array.
 * 
 * \param array The array of semaphores used in the gqueue.
 * \param id Identifier of the task.
 * \return __PO_HI_SUCCESS if successful.
 * \return the result of that function applied to the specified semaphore if there is an error.
 */
int __po_hi_sem_mutex_wait_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);

/**
 * \brief Used to do the po_hi_sem_release function on a semaphore contained in the semaphore array.
 * 
 * \param array The array of semaphores used in the gqueue.
 * \param id Identifier of the task.
 * \return __PO_HI_SUCCESS if successful.
 * \return the result of that function applied to the specified semaphore if there is an error.
 */
int __po_hi_sem_release_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);

/**
 * \brief Used to do the po_hi_sem_mutex_release function on a semaphore contained in the semaphore array.
 * 
 * \param array The array of semaphores used in the gqueue.
 * \param id Identifier of the task.
 * \return __PO_HI_SUCCESS if successful.
 * \return the result of that function applied to the specified semaphore if there is an error.
 */
int __po_hi_sem_mutex_release_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);

#endif /*  __PO_HI_SEMAPHORE_H__ */

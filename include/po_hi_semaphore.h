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


typedef struct
{    
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   //protocol and priority to add
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


/** Basics functions on semaphores */
int __po_hi_sem_init(__po_hi_sem_t* sem, const __po_hi_mutex_protocol_t protocol, const int priority, int nb);
int __po_hi_sem_wait(__po_hi_sem_t* sem);
int __po_hi_sem_mutex_wait(__po_hi_sem_t* sem);
int __po_hi_sem_release(__po_hi_sem_t* sem);
int __po_hi_sem_mutex_release(__po_hi_sem_t* sem);


/** Functions used to fill the __po_hi_gqueues_semaphores array */
int __po_hi_sem_init_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);
int __po_hi_sem_wait_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);
int __po_hi_sem_mutex_wait_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);
int __po_hi_sem_release_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);
int __po_hi_sem_mutex_release_gqueue(__po_hi_sem_t array[__PO_HI_NB_TASKS], __po_hi_task_id id);





#endif /*  __PO_HI_SEMAPHORE_H__ */

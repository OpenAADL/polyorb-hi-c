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

#include <stdint.h>
#include <deployment.h>

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


typedef enum
{
   __PO_HI_PROTECTED_REGULAR     = 1,
   __PO_HI_SEM_REGULAR         = 1,
   __PO_HI_PROTECTED_PIP         = 2,
   __PO_HI_SEM_PIP             = 2,
   __PO_HI_PROTECTED_PCP         = 3,
   __PO_HI_SEM_PCP             = 3,
   __PO_HI_PROTECTED_IPCP        = 4,
   __PO_HI_SEM_IPCP            = 4,
   __PO_HI_PROTECTED_INVALID     = 1
}__po_hi_protected_protocol_t;

typedef __po_hi_protected_protocol_t __po_hi_sem_protocol_t;

typedef struct
{
   __po_hi_sem_protocol_t   protocol;
   int                        priority;
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   pthread_mutex_t      posix_mutex;
   pthread_mutexattr_t  posix_mutexattr;
#endif
#if defined (__PO_HI_RTEMS_CLASSIC_API)
   rtems_id             rtems_sem;
#endif
#if defined (XENO_NATIVE)
   RT_MUTEX             xeno_mutex;
#endif
#if defined (_WIN32)
   HANDLE               win32_mutex;
#endif
}__po_hi_sem_t;



int __po_hi_sem_init(void);
int __po_hi_sem_wait(__po_hi_sem_t* mutex);
int __po_hi_sem_release(__po_hi_sem_t* mutex);





//sem_t inut si pthread mutex_t
//semaphore.h dans quel cas
//protected _protocol_t?
//mtuex df comme binary protocol
//on vire les mutex aprtout













#endif /*  __PO_HI_SEMAPHORE_H__ */

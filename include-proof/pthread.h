/**********************************************************************
 * This is an extract from pthread.h. Only necessary functions for the
 * proof of PolyORB-HI/C are included.
 *
 * TODO: license etc.
 **********************************************************************/

#ifndef _PTHREAD_H
#define _PTHREAD_H	1

#include <features.h>
#include <endian.h>
#include <time.h>

#include <bits/pthreadtypes.h>
#include "__fc_machdep.h"

enum
{
  PTHREAD_CREATE_JOINABLE,
#define PTHREAD_CREATE_JOINABLE	PTHREAD_CREATE_JOINABLE
  PTHREAD_CREATE_DETACHED
#define PTHREAD_CREATE_DETACHED	PTHREAD_CREATE_DETACHED
};


/* Mutex types.  */
enum
{
  PTHREAD_MUTEX_TIMED_NP,
  PTHREAD_MUTEX_RECURSIVE_NP,
  PTHREAD_MUTEX_ERRORCHECK_NP,
  PTHREAD_MUTEX_ADAPTIVE_NP
#if defined __USE_UNIX98 || defined __USE_XOPEN2K8
  ,
  PTHREAD_MUTEX_NORMAL = PTHREAD_MUTEX_TIMED_NP,
  PTHREAD_MUTEX_RECURSIVE = PTHREAD_MUTEX_RECURSIVE_NP,
  PTHREAD_MUTEX_ERRORCHECK = PTHREAD_MUTEX_ERRORCHECK_NP,
  PTHREAD_MUTEX_DEFAULT = PTHREAD_MUTEX_NORMAL
#endif
#ifdef __USE_GNU
  /* For compatibility.  */
  , PTHREAD_MUTEX_FAST_NP = PTHREAD_MUTEX_TIMED_NP
#endif
};


/* Necessary functions for po_hi_time.c */

/* Initialize a mutex.  */
extern int pthread_mutex_init (pthread_mutex_t *__mutex,
			       const pthread_mutexattr_t *__mutexattr);

/* Destroy a mutex.  */
extern int pthread_mutex_destroy (pthread_mutex_t *__mutex);

/* Unlock a mutex.  */
extern int pthread_mutex_unlock (pthread_mutex_t *__mutex);

/* Initialize condition variable COND using attributes ATTR, or use
   the default values if later is NULL.  */
extern int pthread_cond_init (pthread_cond_t *__restrict __cond,
			      const pthread_condattr_t *__restrict __cond_attr);

/* Destroy condition variable COND.  */
extern int pthread_cond_destroy (pthread_cond_t *__cond);

#endif

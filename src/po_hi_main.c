/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2009, GET-Telecom Paris.
 */

#include <pthread.h>

/* system-dependent included files */

#include <po_hi_config.h>
#include <po_hi_returns.h>
#include <po_hi_task.h>
#include <po_hi_protected.h>
/* included files from PolyORB-HI-C */

#include <deployment.h>
/* included files from the generated code */

int __po_hi_transport_need_receiver_task();
void __po_hi_initialize_transport ();

pthread_cond_t cond_init;
pthread_mutex_t mutex_init;

int initialized_tasks;
int nb_tasks_to_init;

int __po_hi_initialize ()
{
  if (pthread_mutex_init (&mutex_init, NULL) != 0 )
    {
      return (__PO_HI_ERROR_PTHREAD_MUTEX);
    }

  /* The barrier is initialized with __PO_HI_NB_TASKS +1
   * members, because the main function must pass the barrier
   */
  nb_tasks_to_init = __PO_HI_NB_TASKS + 1;

#if __PO_HI_NB_NODES > 1
  if (__po_hi_transport_need_receiver_task())
  {
     nb_tasks_to_init++;
  }
#endif

  initialized_tasks = 0;

  if (pthread_cond_init (&cond_init, 
			 NULL) != 0)
    {
      return (__PO_HI_ERROR_PTHREAD_COND);
    }

  __po_hi_initialize_tasking ();

  /* Initialize protected objects */
#if __PO_HI_NB_PROTECTED > 0
  __po_hi_protected_init();
#endif

#if __PO_HI_NB_NODES > 1
  /* We initialize the transport only if
   * the node have servers*/
  __po_hi_initialize_transport ();
#endif

  return (__PO_HI_SUCCESS);
}

int __po_hi_wait_initialization ()
{
  if (pthread_mutex_lock (&mutex_init) != 0)
    return (__PO_HI_ERROR_PTHREAD_MUTEX);

  initialized_tasks++;
  while (initialized_tasks < nb_tasks_to_init)
    {
      pthread_cond_wait (&cond_init, &mutex_init);
    }
  pthread_cond_broadcast (&cond_init);
  pthread_mutex_unlock (&mutex_init);
  return (__PO_HI_SUCCESS);
}

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
#include <po_hi_types.h>

#include <pthread.h>

#include <deployment.h>

#ifndef __PO_HI_NB_PROTECTED
#define __PO_HI_NB_PROTECTED 0
#endif

#if __PO_HI_NB_PROTECTED > 0

/* Declare only needed mutexes according to the generated
 * declarations. The __PO_HI_NB_PROTECTED is a generated macro that
 * represents the needed number of mutexes in the system.
 */

pthread_mutex_t mutexes[__PO_HI_NB_PROTECTED];

int __po_hi_protected_init ()
{
  __po_hi_uint8_t i;

  for (i = 0 ; i < __PO_HI_NB_PROTECTED ; i++ )
    {
      if (pthread_mutex_init (&mutexes[i], NULL) != 0)
	{
	  return __PO_HI_ERROR_PTHREAD_MUTEX;
	}
    }
  return (__PO_HI_SUCCESS);
}

int __po_hi_protected_lock (__po_hi_protected_t protected_id)
{
  if (pthread_mutex_lock (&mutexes[protected_id]) != 0 )
    {
      return __PO_HI_ERROR_PTHREAD_MUTEX;
    }
  return __PO_HI_SUCCESS;
}

int __po_hi_protected_unlock (__po_hi_protected_t protected_id)
{
  if (pthread_mutex_unlock (&mutexes[protected_id]) != 0 )
    {
      return __PO_HI_ERROR_PTHREAD_MUTEX;
    }
  return __PO_HI_SUCCESS;
}

#endif /* __PO_HI_NB_PROTECTED > 0 */

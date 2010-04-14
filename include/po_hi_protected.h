/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2009, GET-Telecom Paris.
 */

#ifndef __PO_HI_PROTECTED_H__
#define __PO_HI_PROTECTED_H__
#include <stdint.h>
#include <deployment.h>

typedef uint8_t __po_hi_protected_t;

int __po_hi_protected_lock (__po_hi_protected_t protected_id);
/*
 * Lock the variable which has he id given by the argument.

 * Return __PO_HI_SUCCESS if it is successfull.  If there is an error,
 * it can return __PO_HI_ERROR_PTHREAD_MUTEX value
 */

int __po_hi_protected_unlock (__po_hi_protected_t protected_id);
/*
 * Unlock the variable which has he id given 
 * by the argument.
 * Return __PO_HI_SUCCESS if it is successfull.
 * If there is an error, it can return 
 * __PO_HI_ERROR_PTHREAD_MUTEX value
 */

int __po_hi_protected_init ();
/*
 * Initialize all variables to handle protected
 * objects in PolyORB-HI-C
 */

#endif /*  __PO_HI_PROTECTED_H__ */

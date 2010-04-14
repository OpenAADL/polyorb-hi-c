/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2009, GET-Telecom Paris.
 */

#ifndef __PO_HI_RETURNS_H__
#define __PO_HI_RETURNS_H__

/* Success return code */
#define __PO_HI_SUCCESS                    1

/* Errors from the API */
#define __PO_HI_ERROR_CREATE_TASK         -10
#define __PO_HI_ERROR_CLOCK               -15
#define __PO_HI_ERROR_QUEUE_FULL          -20

/* Errors related to the pthread library */
#define __PO_HI_ERROR_PTHREAD_COND        -50
#define __PO_HI_ERROR_PTHREAD_MUTEX       -51
#define __PO_HI_ERROR_PTHREAD_CREATE      -52
#define __PO_HI_ERROR_PTHREAD_ATTR        -53
#define __PO_HI_ERROR_PTHREAD_SCHED       -54
#define __PO_HI_ERROR_TRANSPORT_SEND      -55
#define __PO_HI_ERROR_PTHREAD_BARRIER     -56

/* GIOP error code */
#define __PO_HI_GIOP_INVALID_SIZE         -100
#define __PO_HI_GIOP_INVALID_VERSION      -120
#define __PO_HI_GIOP_INVALID_REQUEST_TYPE -150
#define __PO_HI_GIOP_INVALID_OPERATION    -180
#define __PO_HI_GIOP_UNSUPPORTED          -200

#endif /* __RETURNS_H__ */

/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2009, GET-Telecom Paris.
 */

#ifndef __PO_HI_PROTOCOLS__
#define __PO_HI_PROTOCOLS__

#include <po_hi_messages.h>
#include <po_hi_types.h>

#include <deployment.h>
#include <request.h>

#define __PO_HI_NOPORT 1
#define __PO_HI_NOADDR ""

typedef __po_hi_uint16_t __po_hi_inetport_t;
typedef char*            __po_hi_inetaddr_t;

int __po_hi_protocols_send (__po_hi_entity_t from,
			    __po_hi_entity_t to,
			    __po_hi_msg_t* msg);
/*
 * Send a message to a specified entity.  The "from" argument is the
 * node which send the message. The argument "to" is used to designate
 * the entity which receive the message. Finally, the last argument
 * (msg) is the message
 */

int __po_hi_protocols_receive (__po_hi_entity_t from,
			       __po_hi_msg_t* msg);
/*
 * Receive a message from a specified entity The entity which sent the
 * message is specified by the first argument.  The second argument
 * will contains the received message.
 */

int __po_hi_protocols_nonblocking_receive (__po_hi_entity_t from,
					   __po_hi_msg_t* msg);
/*
 * Receive a message from a specified entity The entity which sent the
 * message is specified by the first argument.  The second argument
 * will contains the received message.  Receive 1 if data was received
 */

#endif /* __PO_HI_PROTOCOLS__ */

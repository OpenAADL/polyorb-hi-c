/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#ifndef __PO_HI_TRANSPORT__
#define __PO_HI_TRANSPORT__

#include <po_hi_messages.h>
#include <deployment.h>
#include <request.h>

typedef uint8_t __po_hi_queue_id;

int __po_hi_transport_receive (__po_hi_entity_t from,
			       __po_hi_msg_t* msg);
/*
 * Receive data from a node. The argument designated the sender of the
 * data. The second argument (msg) is the message which will receive
 * the data. If no message has been received, the function will block
 * the thread.
 */

int __po_hi_transport_nonblocking_receive (__po_hi_entity_t from,
					   __po_hi_msg_t* msg);
/* Try to receive data from the node designed by the first
   argument. The data are stored in the second argument.  Returns
   __PO_HI_RECEIVE_SUCCESS if it receives data.  Else, it returns
   __PO_HI_RECEIVE_ERROR if no data are available
*/

void __po_hi_initialize_transport ();
/*
 * Initialize the transport layer (create and initialize
 * variables, ...)
 */

int __po_hi_transport_send (__po_hi_entity_t from,
			    __po_hi_entity_t to,
			    __po_hi_msg_t* msg);
/*
 * Send a message to a specified entity.  The "from" argument is the
 * node which send the message. The argument "to" is used to designate
 * the entity which receive the message. Finally, the last argument
 * (msg) is the message
 */

void __po_hi_initialize_transport_low_level ();
/*
 * Initialize low-level transport driver. It creates all structures
 * and variables required.
 */

int __po_hi_transport_low_level_send (__po_hi_entity_t from, 
				      __po_hi_entity_t to, 
				      __po_hi_msg_t* msg);
/*
 * Send the data through the low-level driver. The first argument is
 * the node which will receive the data. Argument msg is the message
 * which is sent.
 */

#endif /* __PO_HI_TRANSPORT__ */

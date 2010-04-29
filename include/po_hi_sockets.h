/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2010, European Space Agency.
 */

#include <deployment.h>
/* Include generated files */

#include <po_hi_protocols.h>
/* Files from PolyORB-HI-C */

extern __po_hi_node_t mynode;
extern __po_hi_inetport_t node_port[__PO_HI_NB_NODES];
extern __po_hi_inetaddr_t node_addr[__PO_HI_NB_NODES];

#define __PO_HI_TRANSPORT_SOCKET_NEED_RECEIVER_TASK()  \
   (node_port[mynode] != __PO_HI_NOPORT)
/*
 * Maccro that declare if we need to activate another thread
 * that receives data from a socket (receiver task)
 */

void __po_hi_sockets_initialize (void);
/*
 * Initialize sockets, create the receiver tasks
 * and sender file descriptors
 */

int __po_hi_sockets_send (__po_hi_entity_t from, __po_hi_entity_t to, __po_hi_msg_t* msg);
/*
 * Send data through the sending socket
 */

void* __po_hi_sockets_receiver_task (void);
/*
 * Task that polls for incoming data 
 * and dispatch it in po-hi-c queues
 */

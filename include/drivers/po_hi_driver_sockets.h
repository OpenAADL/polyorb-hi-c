/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */

#include <deployment.h>

#ifndef __PO_HI_DRIVER_SOCKETS_H__
#define __PO_HI_DRIVER_SOCKETS_H__

typedef struct
{
   int socket;
} __po_hi_inetnode_t;


#if (defined (__PO_HI_NEED_DRIVER_SOCKETS)  \
  || defined (__PO_HI_NEED_DRIVER_RTEMS_NE2000_SOCKETS))

#include <po_hi_transport.h>

#include <drivers/configuration/ip.h>

#include <po_hi_types.h>

typedef __po_hi_uint16_t __po_hi_inetport_t;
typedef char*            __po_hi_inetaddr_t;

#define __PO_HI_NOPORT 1
#define __PO_HI_NOADDR ""

extern __po_hi_node_t      __po_hi_mynode;


#include <sys/time.h>
#define __PO_HI_SET_SOCKET_TIMEOUT(mysocket,nsec) { struct timeval timeout; \
                                         timeout.tv_sec = 0; \
                                         timeout.tv_usec = nsec; \
                                         setsockopt (mysocket, SOL_SOCKET, SO_RCVTIMEO, (char *)&timeout,sizeof (timeout)); }


#define __PO_HI_TRANSPORT_SOCKET_NEED_RECEIVER_TASK()  \
   (node_port[mynode] != __PO_HI_NOPORT)
/*
 * Maccro that declare if we need to activate another thread
 * that receives data from a socket (receiver task)
 */


void __po_hi_driver_sockets_receiver (void);

int __po_hi_driver_sockets_send (__po_hi_task_id task_id,
                                 __po_hi_port_t port);
/*
 * Send data through the sending socket
 */

void* __po_hi_sockets_receiver_task (void);
/*
 * Task that polls for incoming data 
 * and dispatch it in po-hi-c queues
 */

void* __po_hi_sockets_poller (__po_hi_device_id* dev_id_addr);
/*
 * Generic poller for PO-HI-C protocol.
 */

void __po_hi_driver_sockets_init (__po_hi_device_id id);
#endif

#endif

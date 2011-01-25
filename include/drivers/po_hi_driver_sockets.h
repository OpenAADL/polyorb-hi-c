/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <deployment.h>

#ifndef __PO_HI_DRIVER_SOCKETS_H__
#define __PO_HI_DRIVER_SOCKETS_H__


#if (defined (__PO_HI_NEED_DRIVER_SOCKETS)  \
  || defined (__PO_HI_NEED_DRIVER_RTEMS_NE2000_SOCKETS))

#include <po_hi_transport.h>

typedef __po_hi_uint16_t __po_hi_inetport_t;
typedef char*            __po_hi_inetaddr_t;

#define __PO_HI_NOPORT 1
#define __PO_HI_NOADDR ""

typedef struct
{
   int socket;
} __po_hi_inetnode_t;

extern __po_hi_node_t      __po_hi_mynode;


/* We only need to set the timeout for the NE2000 driver socket.
 * So, this function is used only for this driver.
 */
#ifdef __PO_HI_NEED_DRIVER_RTEMS_NE2000_SOCKETS
   #include <sys/time.h>
   #define __PO_HI_SET_SOCKET_TIMEOUT(mysocket,nsec) { struct timeval timeout; \
                                            timeout.tv_sec = nsec; \
                                            timeout.tv_usec = 0; \
                                            setsockopt (mysocket, SOL_SOCKET, SO_RCVTIMEO, (char *)&timeout,sizeof (timeout)); }
#else
   #define __PO_HI_SET_SOCKET_TIMEOUT(mysocket,nsec)
#endif


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

void* __po_hi_sockets_poller (void);
/*
 * Generic poller for PO-HI-C protocol.
 */

void __po_hi_driver_sockets_init (__po_hi_device_id id);
#endif

#endif


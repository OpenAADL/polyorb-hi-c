/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2010, European Space Agency
 */

#ifndef __PO_HI_DRIVER_SOCKETS_COMMON_H__
#define __PO_HI_DRIVER_SOCKETS_COMMON_H__

#include <deployment.h>

typedef __po_hi_uint16_t __po_hi_inetport_t;
typedef char*            __po_hi_inetaddr_t;


#if (defined (__PO_HI_NEED_DRIVER_SOCKETS)  \
               || defined (__PO_HI_NEED_DRIVER_SOCKETS_ASN1) \
               || defined (__PO_HI_NEED_DRIVER_QEMU_NE2000_SOCKETS))

#define __PO_HI_NOPORT 1
#define __PO_HI_NOADDR ""



typedef struct
{
   int socket;
} __po_hi_inetnode_t;

extern __po_hi_inetport_t node_port[__PO_HI_NB_NODES];
extern __po_hi_inetaddr_t node_addr[__PO_HI_NB_NODES];
extern __po_hi_node_t mynode;

#define __PO_HI_TRANSPORT_SOCKET_NEED_RECEIVER_TASK()  \
   (node_port[mynode] != __PO_HI_NOPORT)
/*
 * Maccro that declare if we need to activate another thread
 * that receives data from a socket (receiver task)
 */

void __po_hi_sockets_init (__po_hi_device_id id);
/*
 * Initialize sockets, create the receiver tasks
 * and sender file descriptors
 */


#endif /* __PO_HI_DRIVER_SOCKETS_COMMON_H__ */
#endif /* __PO_HI_NEED_DRIVER_SOCKETS || __PO_HI_NEED_DRIVER_SOCKETS_ASN1 */



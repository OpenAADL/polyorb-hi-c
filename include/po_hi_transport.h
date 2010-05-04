/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 * Copyright (C) 2010, European Space Agency.
 */

#ifndef __PO_HI_TRANSPORT__
#define __PO_HI_TRANSPORT__

#include <po_hi_messages.h>
#include <deployment.h>
#include <request.h>

typedef __po_hi_uint16_t __po_hi_inetport_t;
typedef char*            __po_hi_inetaddr_t;

#define __PO_HI_NOPORT 1
#define __PO_HI_NOADDR ""



typedef uint8_t __po_hi_queue_id;

__po_hi_node_t __po_hi_transport_get_node_from_entity (__po_hi_entity_t entity);
/*
 * Returns the node identifier that corresponds to an entity.
 */

int __po_hi_transport_send_default (__po_hi_task_id id, __po_hi_port_t port);
/*
 * Default transport layer
 */

#endif /* __PO_HI_TRANSPORT__ */

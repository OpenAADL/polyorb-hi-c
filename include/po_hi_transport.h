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
#include <drivers/po_hi_driver_sockets_common.h>
#include <deployment.h>
#include <request.h>

#define __PO_HI_BIGENDIAN     0
#define __PO_HI_LITTLEENDIAN  1

#if __PO_HI_NB_PORTS > 0

typedef uint8_t __po_hi_queue_id;

__po_hi_node_t    __po_hi_transport_get_node_from_entity (const __po_hi_entity_t entity);
/*
 * Returns the node identifier that corresponds to an entity.
 */

__po_hi_entity_t  __po_hi_get_entity_from_global_port (const __po_hi_port_t port);
/*
 * Return the entity identifier that own the port in parameters.
 */

int               __po_hi_transport_send_default (__po_hi_task_id id, __po_hi_port_t port);
/*
 * Default transport layer
 */

char* __po_hi_get_port_model_name (const __po_hi_port_t port);

char* __po_hi_get_port_name (const __po_hi_port_t port);

__po_hi_local_port_t __po_hi_get_local_port_from_global_port (const __po_hi_port_t global_port);

__po_hi_uint8_t  __po_hi_get_endianness (const __po_hi_node_t node);
__po_hi_device_id __po_hi_get_device_from_port (const __po_hi_port_t port);

char* __po_hi_get_device_naming (const __po_hi_device_id dev);

__po_hi_uint32_t* __po_hi_get_device_configuration (const __po_hi_device_id);

#endif /* __PO_HI_NB_PORTS > 0 */

#endif /* __PO_HI_TRANSPORT__ */

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

#include <po_hi_config.h>
#include <po_hi_types.h>
#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <drivers/po_hi_driver_sockets.h>
#include <po_hi_giop.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_gqueue.h>

#include <deployment.h>
#include <marshallers.h>
#include <types.h>
#include <activity.h>
#include <request.h>

/*
 * The following arrays are declared in the generated header
 * deployment.h.
 */

extern __po_hi_node_t  entity_table[__PO_HI_NB_ENTITIES];

extern __po_hi_entity_t       __po_hi_port_global_to_entity[__PO_HI_NB_PORTS];
extern __po_hi_local_port_t   __po_hi_port_global_to_local[__PO_HI_NB_PORTS];
extern __po_hi_request_t*     __po_hi_gqueues_most_recent_values[__PO_HI_NB_TASKS];
extern __po_hi_uint8_t*       __po_hi_gqueues_n_destinations[__PO_HI_NB_TASKS];
extern __po_hi_port_t**       __po_hi_gqueues_destinations[__PO_HI_NB_TASKS];

int __po_hi_transport_send_default (__po_hi_task_id id, __po_hi_port_t port)
{
   __po_hi_msg_t         msg;
   __po_hi_request_t*    request;
   __po_hi_port_t*       destinations;
   __po_hi_uint8_t       ndest;
   __po_hi_uint8_t       i;
   __po_hi_local_port_t  local_port;

#if __PO_HI_NB_NODES > 1
   int error;
#endif

   local_port = __po_hi_port_global_to_local[(int)port];
   request = &(__po_hi_gqueues_most_recent_values[id][local_port]);

   if (request->port == -1)
   {
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("Send output task %d, port %d : no value to send\n", 
            id, port);
#endif
      return __PO_HI_SUCCESS;
   }

   destinations = __po_hi_gqueues_destinations[id][local_port];
   ndest = __po_hi_gqueues_n_destinations[id][local_port];

#ifdef __PO_HI_DEBUG
   __DEBUGMSG ("Send value, emitter task %d, emitter port %d, emitter entity %d, destination ports :\n", id,  port, __po_hi_port_global_to_entity[port]);
#endif
   for (i=0;i<ndest;i++)
   {
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("\t%d (entity=%d)\n", 
            destinations[i], 
            __po_hi_port_global_to_entity[destinations[i]]);
#endif
      __po_hi_msg_reallocate (&msg);

      request->port = (__po_hi_port_t) destinations[i];

      __po_hi_marshall_request (request, &msg);

#if __PO_HI_NB_NODES > 1
      error =__po_hi_driver_sockets_send (__po_hi_port_global_to_entity[port],
                                          __po_hi_port_global_to_entity[destinations[i]],
                                          &msg);
      if (error != __PO_HI_SUCCESS) 
      {
         return error;
      }
#endif
   }
   request->port = __PO_HI_GQUEUE_INVALID_PORT;

#ifdef __PO_HI_DEBUG
   __DEBUGMSG ("\n");
#endif

   return __PO_HI_SUCCESS;
}



__po_hi_node_t __po_hi_transport_get_node_from_entity (const __po_hi_entity_t entity)
{
   return entity_table[entity];
}

__po_hi_entity_t __po_hi_get_entity_from_global_port (const __po_hi_port_t port)
{
    return __po_hi_port_global_to_entity[port];
}

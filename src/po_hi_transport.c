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
extern char*                  __po_hi_port_global_model_names[__PO_HI_NB_PORTS];
extern char*                  __po_hi_port_global_names[__PO_HI_NB_PORTS];
extern __po_hi_uint8_t        __po_hi_deployment_endiannesses[__PO_HI_NB_NODES];
extern __po_hi_device_id      __po_hi_port_to_device[__PO_HI_NB_PORTS];
extern char*                  __po_hi_devices_naming[__PO_HI_NB_DEVICES];

int __po_hi_transport_send_default (__po_hi_task_id id, __po_hi_port_t port)
{
   __po_hi_msg_t         msg;
   __po_hi_request_t*    request;
   __po_hi_uint8_t       ndest;
   __po_hi_uint8_t       i;
   __po_hi_local_port_t  local_port;
   __po_hi_port_t        destination_port; 
   __po_hi_entity_t      destination_entity;

#if defined (__PO_HI_NEED_DRIVER_SOCKETS) && (__PO_HI_NB_NODES > 1)
   int error;
#endif

   local_port  = __po_hi_get_local_port_from_global_port (port);
   request     = __po_hi_gqueue_get_most_recent_value (id, local_port);

   if (request->port == -1)
   {
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("Send output task %d, port %d : no value to send\n", id, port);
#endif
      return __PO_HI_SUCCESS;
   }

   ndest          = __po_hi_gqueue_get_destinations_number (id, local_port);

#ifdef __PO_HI_DEBUG
   __DEBUGMSG ("Send value, emitter task %d, emitter port %d, emitter entity %d, destination ports :\n", id,  port, __po_hi_port_global_to_entity[port]);
#endif
   for (i=0 ; i < __po_hi_gqueue_get_destinations_number (id, local_port) ; i++)
   {
      destination_port     = __po_hi_gqueue_get_destination (id, local_port, i);
      destination_entity   = __po_hi_get_entity_from_global_port (destination_port);
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("\t%d (entity=%d)", 
            destination_port,
            destination_entity);
#endif
      __po_hi_msg_reallocate (&msg);

      request->port = destination_port;

      if (__po_hi_transport_get_node_from_entity (__po_hi_get_entity_from_global_port (port)) ==
          __po_hi_transport_get_node_from_entity (__po_hi_get_entity_from_global_port (destination_port)))
      {
            __DEBUGMSG (" [deliver locally]\n");
            __po_hi_main_deliver (request);
      }
#if defined (__PO_HI_NEED_DRIVER_SOCKETS) && (__PO_HI_NB_NODES > 1)
      else
      {
         __DEBUGMSG (" [deliver using network sockets]");
         __po_hi_marshall_request (request, &msg);

         error =__po_hi_driver_sockets_send (__po_hi_port_global_to_entity[port],
                                             __po_hi_port_global_to_entity[destination_port],
                                             &msg);
         if (error != __PO_HI_SUCCESS) 
         {
            return error;
         }
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

char* __po_hi_get_port_name (const __po_hi_port_t port)
{
      return (__po_hi_port_global_names[port]);
}


char* __po_hi_get_port_model_name (const __po_hi_port_t port)
{
      return (__po_hi_port_global_model_names[port]);
}

__po_hi_local_port_t __po_hi_get_local_port_from_global_port (const __po_hi_port_t global_port)
{
   return (__po_hi_port_global_to_local[global_port]);
}

__po_hi_uint8_t __po_hi_get_endianness (const __po_hi_node_t node)
{
   return __po_hi_deployment_endiannesses[node];
}

char* __po_hi_get_naming (const __po_hi_port_t port)
{
      return __po_hi_devices_naming[port];
}

__po_hi_device_id __po_hi_get_device_from_port (const __po_hi_port_t port)
{
      return __po_hi_port_to_device[port];
}

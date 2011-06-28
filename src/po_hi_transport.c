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

extern __po_hi_node_t         __po_hi_entity_table[__PO_HI_NB_ENTITIES];

extern __po_hi_entity_t       __po_hi_port_global_to_entity[__PO_HI_NB_PORTS];
extern __po_hi_local_port_t   __po_hi_port_global_to_local[__PO_HI_NB_PORTS];
extern __po_hi_request_t*     __po_hi_gqueues_most_recent_values[__PO_HI_NB_TASKS];
extern char*                  __po_hi_port_global_model_names[__PO_HI_NB_PORTS];
extern char*                  __po_hi_port_global_names[__PO_HI_NB_PORTS];
extern __po_hi_uint8_t        __po_hi_deployment_endiannesses[__PO_HI_NB_NODES];

#if __PO_HI_NB_DEVICES > 0
extern __po_hi_device_id      __po_hi_port_to_device[__PO_HI_NB_PORTS];
extern char*                  __po_hi_devices_naming[__PO_HI_NB_DEVICES];
extern __po_hi_uint32_t*      __po_hi_devices_configuration_values[__PO_HI_NB_DEVICES];
#endif

#ifdef XM3_RTEMS_MODE

#include <deployment.h>
#include <po_hi_types.h>
#include <po_hi_transport.h>
#include <xm.h>
int                           __po_hi_xtratum_port[__PO_HI_NB_PORTS];
#endif


int __po_hi_transport_send_default (__po_hi_task_id id, __po_hi_port_t port)
{
   __po_hi_msg_t         msg;
   __po_hi_request_t*    request;
   __po_hi_uint8_t       ndest;
   __po_hi_uint8_t       i;
   __po_hi_local_port_t  local_port;
   __po_hi_port_t        destination_port; 
   __po_hi_entity_t      destination_entity;

   local_port  = __po_hi_get_local_port_from_global_port (port);
   request     = __po_hi_gqueue_get_most_recent_value (id, local_port);

   if (request->port == -1)
   {
      __PO_HI_DEBUG_DEBUG ("Send output task %d, port %d : no value to send\n", id, port);
      return __PO_HI_SUCCESS;
   }

   ndest          = __po_hi_gqueue_get_destinations_number (id, local_port);

   __PO_HI_DEBUG_DEBUG ("Send value, emitter task %d, emitter port %d, emitter entity %d, destination ports :\n", id,  port, __po_hi_port_global_to_entity[port]);

#if __PO_HI_DEBUG_LEVEL >= __PO_HI_DEBUG_LEVEL_INFO
   __DEBUGMSG ("SENT Value: |");
   {
         int s;
         int i;
         unsigned int* tmp;
         tmp = (unsigned int*) &request->vars;
         s = sizeof (request->vars);
         for (i = 0 ; i < s ; i+=4)
         {
            __DEBUGMSG("%x", *tmp);
            tmp++;
            fflush (stdout);
         }
   }
   __DEBUGMSG ("|\n");
#endif

   for (i=0 ; i < __po_hi_gqueue_get_destinations_number (id, local_port) ; i++)
   {
      destination_port     = __po_hi_gqueue_get_destination (id, local_port, i);
      destination_entity   = __po_hi_get_entity_from_global_port (destination_port);
      __PO_HI_DEBUG_DEBUG ("\t%d (entity=%d)", destination_port, destination_entity);
      __po_hi_msg_reallocate (&msg);

      request->port = destination_port;

      if (__po_hi_transport_get_node_from_entity (__po_hi_get_entity_from_global_port (port)) ==
          __po_hi_transport_get_node_from_entity (__po_hi_get_entity_from_global_port (destination_port)))
      {
            __PO_HI_DEBUG_DEBUG (" [deliver locally]\n");
            __po_hi_main_deliver (request);
      }
#ifdef XM3_RTEMS_MODE
      else
      {
         __po_hi_port_kind_t pkind = __po_hi_transport_get_port_kind (port);
         int ret;
         ret = -1;
         if (pkind == __PO_HI_OUT_DATA_INTER_PROCESS)
         {
            ret = XM_write_sampling_message (__po_hi_xtratum_port[port], request, sizeof (__po_hi_request_t));
         }

         if (pkind == __PO_HI_OUT_EVENT_DATA_INTER_PROCESS)
         {
            ret = XM_send_queuing_message (__po_hi_xtratum_port[port], request, sizeof (__po_hi_request_t));
         }

         if (ret < 0)
         {
            __PO_HI_DEBUG_DEBUG ("[GQUEUE] Cannot deliver the data using inter-partitions ports, return=%d\n", ret);
         }
         else
         {
            __PO_HI_DEBUG_DEBUG ("[GQUEUE] Data delivered using inter-partitions ports, return=%d\n", ret);
         }
      }
#endif
   }
   request->port = __PO_HI_GQUEUE_INVALID_PORT;

#ifdef __PO_HI_DEBUG
   __PO_HI_DEBUG_DEBUG ("\n");
#endif

   return __PO_HI_SUCCESS;
}

__po_hi_node_t __po_hi_transport_get_node_from_entity (const __po_hi_entity_t entity)
{
   return __po_hi_entity_table[entity];
}

__po_hi_node_t __po_hi_transport_get_mynode (void)
{
   extern __po_hi_node_t __po_hi_mynode;
   return (__po_hi_mynode);
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

#if __PO_HI_NB_DEVICES > 0
char* __po_hi_get_device_naming (const __po_hi_device_id dev)
{
      return __po_hi_devices_naming[dev];
}

__po_hi_device_id __po_hi_get_device_from_port (const __po_hi_port_t port)
{
      return __po_hi_port_to_device[port];
}

__po_hi_uint32_t* __po_hi_get_device_configuration (const __po_hi_device_id dev)
{
   if (dev > __PO_HI_NB_DEVICES)
   {
      return NULL;
   }
   return __po_hi_devices_configuration_values[dev];
}

#endif


char* __po_hi_transport_get_model_name (const __po_hi_port_t portno)
{
   extern char*                  __po_hi_port_global_model_names[__PO_HI_NB_PORTS];

   if (portno >= __PO_HI_NB_PORTS)
   {
      __DEBUGMSG ("[TRANSPORT] Try to get the name of a non-existing port\n");
      return NULL;
   }
   else
   {
      return __po_hi_port_global_model_names[portno];
   }
}


__po_hi_uint32_t __po_hi_transport_get_queue_size (const __po_hi_port_t portno)
{
   extern __po_hi_uint32_t __po_hi_port_global_queue_size[__PO_HI_NB_PORTS];

   if (portno >= __PO_HI_NB_PORTS)
   {
      __DEBUGMSG ("[TRANSPORT] Try to get the queue size of a non-existing port\n");
      return 1;
   }
   else
   {
      return __po_hi_port_global_queue_size[portno];
   }
}

__po_hi_uint32_t __po_hi_transport_get_data_size (const __po_hi_port_t portno)
{
   extern __po_hi_uint32_t __po_hi_port_global_data_size[__PO_HI_NB_PORTS];

   if (portno >= __PO_HI_NB_PORTS)
   {
      __DEBUGMSG ("[TRANSPORT] Try to get the data size of a non-existing port\n");
      return 1;
   }
   else
   {
      return __po_hi_port_global_data_size[portno];
   }
}

__po_hi_port_kind_t __po_hi_transport_get_port_kind (const __po_hi_port_t portno)
{
   extern __po_hi_port_kind_t    __po_hi_port_global_kind[__PO_HI_NB_PORTS];
   if (portno >= __PO_HI_NB_PORTS)
   {
      __DEBUGMSG ("[TRANSPORT] Try to get the type/kind of a non-existing port\n");
      return __PO_HI_INVALID_PORT_KIND;
   }
   else
   {
      return __po_hi_port_global_kind[portno];
   }

}

#ifdef XM3_RTEMS_MODE
void __po_hi_transport_xtratum_port_init (const __po_hi_port_t portno, int val)
{
   __po_hi_xtratum_port[portno] = val;
}

int __po_hi_transport_xtratum_get_port (const __po_hi_port_t portno)
{
   return __po_hi_xtratum_port[portno];
}
#endif



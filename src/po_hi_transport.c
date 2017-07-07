/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2017 ESA & ISAE.
 */

#include<stddef.h>
#include<assert.h>

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

extern __po_hi_node_t            __po_hi_entity_table[__PO_HI_NB_ENTITIES];
extern __po_hi_entity_t          __po_hi_port_global_to_entity[__PO_HI_NB_PORTS];
extern __po_hi_local_port_t      __po_hi_port_global_to_local[__PO_HI_NB_PORTS];
extern __po_hi_request_t*        __po_hi_gqueues_most_recent_values[__PO_HI_NB_TASKS];
extern char*                     __po_hi_port_global_model_names[__PO_HI_NB_PORTS];
extern char*                     __po_hi_port_global_names[__PO_HI_NB_PORTS];
extern __po_hi_uint8_t           __po_hi_deployment_endiannesses[__PO_HI_NB_NODES];
extern __po_hi_protocol_conf_t   __po_hi_protocols_configuration[__PO_HI_NB_PROTOCOLS];

#if __PO_HI_NB_DEVICES > 0
__po_hi_transport_sending_func            __po_hi_transport_devices_sending_funcs[__PO_HI_NB_DEVICES];
extern __po_hi_port_t                     __po_hi_devices_to_nodes[__PO_HI_NB_DEVICES];
extern __po_hi_port_t                     __po_hi_devices_to_nodes[__PO_HI_NB_DEVICES];
extern __po_hi_device_id                  __po_hi_port_to_device[__PO_HI_NB_PORTS];
extern char*                              __po_hi_devices_naming[__PO_HI_NB_DEVICES];
extern __po_hi_uint32_t*                  __po_hi_devices_configuration_values[__PO_HI_NB_DEVICES];
extern __po_hi_uint32_t                   __po_hi_devices_nb_accessed_buses[__PO_HI_NB_DEVICES];
extern __po_hi_bus_id*                    __po_hi_devices_accessed_buses[__PO_HI_NB_DEVICES];
#endif

#if __PO_HI_NB_PROTOCOLS > 0
extern __po_hi_protocol_t        __po_hi_ports_protocols[__PO_HI_NB_PORTS][__PO_HI_NB_PORTS];
#endif

#ifdef XM3_RTEMS_MODE

#include <deployment.h>
#include <po_hi_types.h>
#include <po_hi_transport.h>
#include <xm.h>
int                           __po_hi_xtratum_port[__PO_HI_NB_PORTS];
#endif


int __po_hi_transport_send (__po_hi_task_id id, __po_hi_port_t port)
{
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
   assert(ndest);
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
      assert(destination_entity != -1);
      __PO_HI_DEBUG_DEBUG ("\t%d (entity=%d)", destination_port, destination_entity);

      request->port = destination_port;

      if (__po_hi_transport_get_node_from_entity (__po_hi_get_entity_from_global_port (port)) ==
          __po_hi_transport_get_node_from_entity (__po_hi_get_entity_from_global_port (destination_port)))
      {
            __PO_HI_DEBUG_DEBUG (" [deliver locally]\n");
            __po_hi_main_deliver (request);
      }
#ifndef XM3_RTEMS_MODE
      else
      {
            __PO_HI_DEBUG_DEBUG (" [deliver remotely]\n");
            __po_hi_transport_call_sending_func_by_port (id, port);
      }
#else /* for XTratuM */
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
            __PO_HI_DEBUG_CRITICAL ("[GQUEUE] Cannot deliver the data using inter-partitions ports, return=%d\n", ret);
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
int __po_hi_transport_call_sending_func_by_port (__po_hi_task_id task_id, __po_hi_port_t port)
{
   __po_hi_device_id device =__po_hi_get_device_from_port (port);

   __PO_HI_DEBUG_DEBUG ("[TRANSPORT] Calling function for device %d\n", device);
   if (device != invalid_device_id)
   {
      return __po_hi_transport_call_sending_func_by_device (device, task_id, port);
   }
   return __PO_HI_UNAVAILABLE;
}

int __po_hi_transport_call_sending_func_by_device (const __po_hi_device_id device, __po_hi_task_id task_id, __po_hi_port_t port)
{
   __po_hi_transport_sending_func send_func;
   send_func = __po_hi_transport_get_sending_func (device);

   if (send_func == NULL)
   {
      return __PO_HI_UNAVAILABLE;
   }
   return send_func (task_id, port);
}


__po_hi_transport_sending_func __po_hi_transport_get_sending_func (const __po_hi_device_id device)
{
   if (device > __PO_HI_NB_DEVICES)
   {
      return NULL;
   }

   return __po_hi_transport_devices_sending_funcs[device];
}

int __po_hi_transport_set_sending_func (const __po_hi_device_id device, const __po_hi_transport_sending_func func)
{
   if (device > __PO_HI_NB_DEVICES)
   {
      return __PO_HI_UNAVAILABLE;
   }

   __po_hi_transport_devices_sending_funcs[device] = func;

   return 0;
}


int __po_hi_transport_associate_port_bus (const __po_hi_port_t port, const __po_hi_bus_id bus)
{
   __po_hi_device_id current_device;
   __po_hi_node_t    current_node;
   __po_hi_bus_id*   tmp_buses;
   __po_hi_uint32_t  tmp_n_buses;
   __po_hi_uint32_t  tmp;
   __po_hi_node_t    tmp_node;
   __po_hi_device_id tmp_device;

   if (port > __PO_HI_NB_PORTS)
   {
      return 0;
   }

   current_device = __po_hi_get_device_from_port (port);

   if (current_device == invalid_device_id)
   {
      return 0;
   }

   current_node = __po_hi_transport_get_node_from_device (current_device);

   for (tmp_device=0 ; tmp_device < __PO_HI_NB_DEVICES ; tmp_device++)
   {
      if (tmp_device == current_device)
      {
         continue;
      }

      tmp_buses      = __po_hi_transport_get_accessed_buses (tmp_device);
      tmp_n_buses    = __po_hi_transport_get_n_accessed_buses (tmp_device);
      tmp_node       = __po_hi_transport_get_node_from_device (tmp_device);

      if (tmp_node != current_node)
      {
         continue;
      }

      for (tmp = 0 ; tmp < tmp_n_buses ; tmp++)
      {
         if (tmp_buses[tmp] == bus)
         {

            __po_hi_port_to_device[port] = tmp_device;
            return 1;
         }
      }
   }
   return 0;
}


int __po_hi_transport_share_bus (const __po_hi_device_id first, const __po_hi_device_id second)
{
   __po_hi_uint32_t i;
   __po_hi_uint32_t j;
   __po_hi_uint32_t first_n_buses;
   __po_hi_uint32_t second_n_buses;

   __po_hi_bus_id* first_buses;
   __po_hi_bus_id* second_buses;

   first_buses       = __po_hi_transport_get_accessed_buses (first);
   second_buses      = __po_hi_transport_get_accessed_buses (second);

   first_n_buses     = __po_hi_transport_get_n_accessed_buses (first);
   second_n_buses    = __po_hi_transport_get_n_accessed_buses (second);

   for (i = 0 ; i < first_n_buses ; i++)
   {
      for (j = 0 ; j < second_n_buses ; j++)
      {
         if (first_buses[i] == second_buses[j])
         {
            return 1;
         }
      }
   }
   return 0;
}


__po_hi_bus_id* __po_hi_transport_get_accessed_buses (const __po_hi_device_id device)
{
   if ((device < 0) || (device >= __PO_HI_NB_DEVICES))
   {
      return NULL;
   }
   return __po_hi_devices_accessed_buses[device];
}


uint32_t __po_hi_transport_get_n_accessed_buses (const __po_hi_device_id device)
{
   if ((device < 0) || (device >= __PO_HI_NB_DEVICES))
   {
      return 0;
   }
   return __po_hi_devices_nb_accessed_buses[device];

}

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

__po_hi_node_t    __po_hi_transport_get_node_from_device (const __po_hi_device_id device)
{
   return (__po_hi_devices_to_nodes[device]);
}
#else
int __po_hi_transport_call_sending_func_by_port (__po_hi_task_id task_id, __po_hi_port_t port)
{
   __DEBUGMSG ("[TRANSPORT] task id %d port %d, nb protocols is less than or equal to zero\n", task_id,port);
   return __PO_HI_UNAVAILABLE;
}
#endif /* __PO_HI_NB_DEVICES > 0 */


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

__po_hi_protocol_t __po_hi_transport_get_protocol (const __po_hi_port_t src, const __po_hi_port_t dst)
{
__po_hi_protocol_t protocol;

#if __PO_HI_NB_PROTOCOLS > 0
   protocol= (__po_hi_ports_protocols[src][dst]);
#else
   __DEBUGMSG ("[TRANSPORT] port SRC=%d DST=%d, nb protocols is less than or equal to zero\n", src,dst);
   protocol= invalid_protocol;
#endif
return protocol;
}

__po_hi_protocol_conf_t*    __po_hi_transport_get_protocol_configuration (const __po_hi_protocol_t p)
{

#if __PO_HI_NB_PROTOCOLS > 0
   if (p == invalid_protocol)
   {
	return NULL;
   }
   else
	return &(__po_hi_protocols_configuration[p]);
#else
   __DEBUGMSG ("[TRANSPORT] protocol %d, nb protocols is less than or equal to zero\n", p);
   return NULL;
#endif
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

/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2009, GET-Telecom Paris.
 */

#include <po_hi_config.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_transport.h>
#include <po_hi_protocols.h>
#include <po_hi_debug.h>
#include <po_hi_gqueue.h>
/* Headers from PolyORB-HI-C */

#include <deployment.h>
#include <activity.h>
#include <request.h>
#include <marshallers.h>
/* Headers from the generated code */

#include <string.h>
#include <pthread.h>
/* System-dependent headers */

#define __PO_HI_GQUEUE_OUT_PORT constant_out_identifier 
/* give a default value to the out port */

extern __po_hi_entity_t       __po_hi_port_global_to_entity[__PO_HI_NB_PORTS];
extern __po_hi_local_port_t   __po_hi_port_global_to_local[__PO_HI_NB_PORTS];

__po_hi_port_t*        __po_hi_gqueues[__PO_HI_NB_TASKS];
__po_hi_int8_t         __po_hi_gqueues_nb_ports[__PO_HI_NB_TASKS];
__po_hi_int8_t*        __po_hi_gqueues_sizes[__PO_HI_NB_TASKS];
__po_hi_uint8_t*       __po_hi_gqueues_used_size[__PO_HI_NB_TASKS];
__po_hi_uint8_t*       __po_hi_gqueues_offsets[__PO_HI_NB_TASKS];
__po_hi_uint8_t*       __po_hi_gqueues_woffsets[__PO_HI_NB_TASKS];
__po_hi_uint8_t*       __po_hi_gqueues_n_destinations[__PO_HI_NB_TASKS];
__po_hi_port_t**       __po_hi_gqueues_destinations[__PO_HI_NB_TASKS];
__po_hi_uint16_t       __po_hi_gqueues_total_fifo_size[__PO_HI_NB_TASKS];
__po_hi_request_t*     __po_hi_gqueues_most_recent_values[__PO_HI_NB_TASKS];
__po_hi_uint8_t*       __po_hi_gqueues_first[__PO_HI_NB_TASKS];

__po_hi_uint8_t        __po_hi_gqueues_global_size[__PO_HI_NB_TASKS];
__po_hi_local_port_t*  __po_hi_gqueues_global_history[__PO_HI_NB_TASKS];
__po_hi_uint16_t       __po_hi_gqueues_global_history_offset[__PO_HI_NB_TASKS];
__po_hi_uint16_t       __po_hi_gqueues_global_history_woffset[__PO_HI_NB_TASKS];

__po_hi_uint8_t*       __po_hi_gqueues_port_is_empty[__PO_HI_NB_TASKS];
__po_hi_uint8_t        __po_hi_gqueues_queue_is_empty[__PO_HI_NB_TASKS];
__po_hi_uint8_t        __po_hi_gqueues_n_empty[__PO_HI_NB_TASKS];

pthread_mutex_t        __po_hi_gqueues_mutexes[__PO_HI_NB_TASKS];
pthread_cond_t         __po_hi_gqueues_conds[__PO_HI_NB_TASKS];
pthread_mutexattr_t    __po_hi_gqueues_mutexes_attr[__PO_HI_NB_TASKS];
pthread_condattr_t     __po_hi_gqueues_conds_attr[__PO_HI_NB_TASKS];

void __po_hi_gqueue_init (  __po_hi_task_id       id,
                            __po_hi_uint8_t       nb_ports,
                            __po_hi_port_t        queue[],
                            __po_hi_int8_t        sizes[],
                            __po_hi_uint8_t       first[],
                            __po_hi_uint8_t       offsets[],
                            __po_hi_uint8_t       woffsets[],
                            __po_hi_uint8_t       n_dest[],
                            __po_hi_port_t*       destinations[],
                            __po_hi_uint8_t       used_size[],
                            __po_hi_local_port_t  history[],
                            __po_hi_request_t     recent[],
                            __po_hi_uint8_t       empties[],
                            __po_hi_uint16_t      total_fifo_size)
{
  __po_hi_uint8_t tmp;
  __po_hi_uint16_t off;
  __po_hi_request_t* request;

  __po_hi_gqueues_global_history_woffset[id] = 0;
  __po_hi_gqueues_global_history_offset[id] = 0;

  __po_hi_gqueues_n_empty[id] = nb_ports;
  __po_hi_gqueues[id] = queue;
  __po_hi_gqueues_most_recent_values[id] = recent;
  __po_hi_gqueues_global_history[id] = history;
  __po_hi_gqueues_woffsets[id] = woffsets;

  __po_hi_gqueues_port_is_empty[id] = empties;

  __po_hi_gqueues_nb_ports[id] = nb_ports; 
  __po_hi_gqueues_sizes[id] = sizes;
  __po_hi_gqueues_first[id] = first;
  __po_hi_gqueues_used_size[id] = used_size;

  __po_hi_gqueues_offsets[id] = offsets;
  __po_hi_gqueues_n_destinations[id] = n_dest;
  __po_hi_gqueues_destinations[id] = destinations;
  __po_hi_gqueues_total_fifo_size[id] = total_fifo_size;

  __po_hi_gqueues_queue_is_empty[id] = 1;

  pthread_mutexattr_init (&__po_hi_gqueues_mutexes_attr[id]);
  pthread_condattr_init (&__po_hi_gqueues_conds_attr[id]);
#ifdef POSIX
  pthread_mutexattr_setpshared(&__po_hi_gqueues_mutexes_attr[id],PTHREAD_PROCESS_SHARED); 
#endif
  pthread_mutex_init (&__po_hi_gqueues_mutexes[id], &__po_hi_gqueues_mutexes_attr[id]);
  pthread_cond_init (&__po_hi_gqueues_conds[id], &__po_hi_gqueues_conds_attr[id]);

  off = 0;

  for (tmp=0;tmp<nb_ports;tmp++)
    {
      __po_hi_gqueues_used_size[id][tmp] = 0;
      if ( (sizes[tmp] != __PO_HI_GQUEUE_FIFO_INDATA) 
	   && (sizes[tmp] != __PO_HI_GQUEUE_FIFO_OUT))
	{
	  __po_hi_gqueues_first[id][tmp]=off;
	  off += __po_hi_gqueues_sizes[id][tmp];
	  __po_hi_gqueues_offsets[id][tmp] = 0;
	  __po_hi_gqueues_woffsets[id][tmp] = 0;
	  __po_hi_gqueues_port_is_empty[id][tmp] = 1;
	}

      /* Set invalid all recent values */
      request = (__po_hi_request_t*)&__po_hi_gqueues_most_recent_values[id][tmp];
      request->port = __PO_HI_GQUEUE_INVALID_PORT;
    }

#ifdef __PO_HI_DEBUG
  __DEBUGMSG("Initialize global queue for task-id %d ... ", id);
  for (tmp=0;tmp<nb_ports;tmp++)
    {
      __DEBUGMSG("port %d (used_size=%d,first=%d) ", 
		 tmp, 
		 __po_hi_gqueues_used_size[id][tmp],
		 __po_hi_gqueues_first[id][tmp]);
    }
  __DEBUGMSG(" ... done\n");
#endif 
}


void __po_hi_gqueue_store_out (__po_hi_task_id id, 
			       __po_hi_local_port_t port, 
			       __po_hi_request_t* request)
{
  __po_hi_request_t* ptr;

  request->port = __PO_HI_GQUEUE_OUT_PORT;
  ptr = &__po_hi_gqueues_most_recent_values[id][port];
  memcpy (ptr, request, sizeof (*request));
}

__po_hi_uint8_t __po_hi_gqueue_store_in (__po_hi_task_id id, 
					 __po_hi_local_port_t port, 
					 __po_hi_request_t* request)
{
  __po_hi_request_t* ptr;
  ptr = &__po_hi_gqueues_most_recent_values[id][port];
#ifdef __PO_HI_DEBUG
  if (ptr == NULL)
    {
      __DEBUGMSG ("__po_hi_gqueue_store_in : NULL POINTER\n");
    }
#endif

  pthread_mutex_lock (&__po_hi_gqueues_mutexes[id]);
  if (__po_hi_gqueues_sizes[id][port] == __PO_HI_GQUEUE_FIFO_INDATA)
    {
      memcpy(ptr,request,sizeof(*request));
    }
  else
    {
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("Received  message for task %d, port %d\n", id, port);
#endif
      if (__po_hi_gqueues_used_size[id][port] == __po_hi_gqueues_sizes[id][port])
	{
	  pthread_mutex_unlock (&__po_hi_gqueues_mutexes[id]);
	  __DEBUGMSG ("QUEUE FULL");
	  return __PO_HI_ERROR_QUEUE_FULL;
	}

      memcpy ((void *)&__po_hi_gqueues[id][port] + ( (__po_hi_gqueues_woffsets[id][port] + __po_hi_gqueues_first[id][port])  * sizeof (*request) ) , request, sizeof (*request));
      __po_hi_gqueues_woffsets[id][port] =  (__po_hi_gqueues_woffsets[id][port] + 1 ) % __po_hi_gqueues_sizes[id][port];

      __po_hi_gqueues_used_size[id][port]++;

      __po_hi_gqueues_global_history[id][__po_hi_gqueues_global_history_woffset[id]] = port;
      __po_hi_gqueues_global_history_woffset[id] = (__po_hi_gqueues_global_history_woffset[id] + 1 ) % __po_hi_gqueues_total_fifo_size[id];

      if (__po_hi_gqueues_port_is_empty[id][port] == 1)
	{
	  __po_hi_gqueues_port_is_empty[id][port] = 0;
	  __po_hi_gqueues_n_empty[id]--;
	}
      __po_hi_gqueues_queue_is_empty[id] = 0;
    }

  pthread_mutex_unlock (&__po_hi_gqueues_mutexes[id]);
  pthread_cond_broadcast (&__po_hi_gqueues_conds[id]);

  return __PO_HI_SUCCESS;
}

int __po_hi_gqueue_send_output (__po_hi_task_id id, __po_hi_port_t port)
{
  __po_hi_msg_t msg;
  __po_hi_request_t* request;
  __po_hi_port_t* destinations;
  __po_hi_uint8_t ndest;
  __po_hi_uint8_t i;
  __po_hi_local_port_t local_port;
  int error;

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
      error =__po_hi_protocols_send
	(__po_hi_port_global_to_entity[port],
	 __po_hi_port_global_to_entity[destinations[i]],
	 &msg);
      if (error != __PO_HI_SUCCESS) 
	{
	  return error;
	}
    }
  request->port = __PO_HI_GQUEUE_INVALID_PORT;

#ifdef __PO_HI_DEBUG
  __DEBUGMSG ("\n");
#endif

  return __PO_HI_SUCCESS;
}

void __po_hi_gqueue_wait_for_incoming_event( __po_hi_task_id id, 
					     __po_hi_local_port_t* port)
{
  pthread_mutex_lock (&__po_hi_gqueues_mutexes[id]);
  while(__po_hi_gqueues_queue_is_empty[id] == 1)
    {
      pthread_cond_wait (&__po_hi_gqueues_conds[id],
			 &__po_hi_gqueues_mutexes[id]);
    }
  *port = __po_hi_gqueues_global_history[id][__po_hi_gqueues_global_history_offset[id]];
  pthread_mutex_unlock (&__po_hi_gqueues_mutexes[id]);
}

int __po_hi_gqueue_get_count( __po_hi_task_id id, __po_hi_local_port_t port)
{
  if (__po_hi_gqueues_sizes[id][port] == __PO_HI_GQUEUE_FIFO_INDATA)
    {
      return 1; /* data port are always of size 1 */
    }
  else
    {
      return (__po_hi_gqueues_used_size[id][port]);
    }
}

int __po_hi_gqueue_get_value( __po_hi_task_id id, 
			      __po_hi_local_port_t port, 
			      __po_hi_request_t* request)
{
  __po_hi_request_t* ptr;
  ptr = &__po_hi_gqueues_most_recent_values[id][port];
  pthread_mutex_lock (&__po_hi_gqueues_mutexes[id]);
        
  /*
   * If the port is an event port, with no value queued, then we block
   * the thread.
   */
  if (__po_hi_gqueues_sizes[id][port] != __PO_HI_GQUEUE_FIFO_INDATA)
    {
      while (__po_hi_gqueues_port_is_empty[id][port] == 1)
	{
	  pthread_cond_wait (&__po_hi_gqueues_conds[id],
			     &__po_hi_gqueues_mutexes[id]);
	}
    }

  if (__po_hi_gqueues_used_size[id][port] == 0)
    {
      memcpy (request, ptr, sizeof (__po_hi_request_t));
    }
  else
    {
      memcpy (request, 
	      (void *)&__po_hi_gqueues[id][port] 
	      + ( __po_hi_gqueues_first[id][port] 
		  + __po_hi_gqueues_offsets[id][port] ) 
	      * sizeof (__po_hi_request_t), 
	      sizeof (__po_hi_request_t));
    }

#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("Task %d get a value on port %d\n", id, port);
#endif

  pthread_mutex_unlock (&__po_hi_gqueues_mutexes[id]);
  return 0;
}

int __po_hi_gqueue_next_value( __po_hi_task_id id, __po_hi_local_port_t port)
{
  /* incomplete semantics, should discriminate and report whether
     there is a next value or not */

  /* XXX change and use assert ? */
  if (__po_hi_gqueues_sizes[id][port] == __PO_HI_GQUEUE_FIFO_INDATA)
    {
      return 1;
    }

  pthread_mutex_lock (&__po_hi_gqueues_mutexes[id]);
  __po_hi_gqueues_offsets[id][port] = 
    (__po_hi_gqueues_offsets[id][port] + 1) 
    % __po_hi_gqueues_sizes[id][port];

  __po_hi_gqueues_used_size[id][port]--;

  if (__po_hi_gqueues_used_size[id][port] == 0)
    {
      __po_hi_gqueues_n_empty[id]++;
      __po_hi_gqueues_port_is_empty[id][port] = 1;
    }
	
  if (__po_hi_gqueues_n_empty[id] == __po_hi_gqueues_nb_ports[id])
    {
      __po_hi_gqueues_queue_is_empty[id] = 1;
    }

  __po_hi_gqueues_global_history_offset[id] = 
    (__po_hi_gqueues_global_history_offset[id] + 1) 
    % __po_hi_gqueues_total_fifo_size[id];

  pthread_mutex_unlock (&__po_hi_gqueues_mutexes[id]);
  return __PO_HI_SUCCESS;
}

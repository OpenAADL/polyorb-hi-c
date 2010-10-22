/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2010, European Space Agency (ESA).
 */

#include <po_hi_config.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_transport.h>
#include <po_hi_debug.h>
#include <po_hi_gqueue.h>
/* Headers from PolyORB-HI-C */

#include <deployment.h>
#include <activity.h>
#include <request.h>
/* Headers from the generated code */

#include <string.h>

#if defined (POSIX) || defined (RTEMS_POSIX)
#include <pthread.h>
#elif defined(RTEMS_PURE)
#include <rtems.h>
#include <inttypes.h>
#include <po_hi_time.h>
#define __PO_HI_DEFAULT_PRIORITY RTEMS_NO_PRIORITY
#endif



#define __PO_HI_GQUEUE_OUT_PORT constant_out_identifier 
/* give a default value to the out port */

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

#if defined (RTEMS_POSIX) || defined (POSIX)
pthread_mutex_t        __po_hi_gqueues_mutexes[__PO_HI_NB_TASKS];
pthread_cond_t         __po_hi_gqueues_conds[__PO_HI_NB_TASKS];
pthread_mutexattr_t    __po_hi_gqueues_mutexes_attr[__PO_HI_NB_TASKS];
pthread_condattr_t     __po_hi_gqueues_conds_attr[__PO_HI_NB_TASKS];
#endif

#ifdef RTEMS_PURE
rtems_id                __po_hi_gqueues_semaphores[__PO_HI_NB_TASKS];
rtems_id                __po_hi_gqueues_barriers[__PO_HI_NB_TASKS];
#endif

void __po_hi_gqueue_init (__po_hi_task_id       id,
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
   __po_hi_uint8_t      tmp;
   __po_hi_uint16_t     off;
   __po_hi_request_t*   request;

#ifdef RTEMS_PURE
   rtems_status_code    ret;
#endif

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

#if defined (RTEMS_POSIX) || defined (POSIX)
   pthread_mutexattr_init (&__po_hi_gqueues_mutexes_attr[id]);
   pthread_condattr_init (&__po_hi_gqueues_conds_attr[id]);
#ifdef POSIX
   pthread_mutexattr_setpshared(&__po_hi_gqueues_mutexes_attr[id],PTHREAD_PROCESS_SHARED); 
#endif
   pthread_mutex_init (&__po_hi_gqueues_mutexes[id], &__po_hi_gqueues_mutexes_attr[id]);
   pthread_cond_init (&__po_hi_gqueues_conds[id], &__po_hi_gqueues_conds_attr[id]);
#endif

#ifdef RTEMS_PURE
   __PO_HI_DEBUG_INFO ("[GQUEUE] Create semaphore for queue of task %d\n", id);
   ret = rtems_semaphore_create (rtems_build_name ('G', 'S', 'E' , 'A' + (char) id), 1, RTEMS_BINARY_SEMAPHORE, __PO_HI_DEFAULT_PRIORITY, &(__po_hi_gqueues_semaphores[id]));
   if (ret != RTEMS_SUCCESSFUL)
   {
      __PO_HI_DEBUG_WARNING ("[GQUEUE] Cannot create semaphore, error code=%d\n", ret);
   }

   __PO_HI_DEBUG_INFO ("[GQUEUE] Create barrier for queue of task %d\n", id);
   ret = rtems_barrier_create (rtems_build_name ('G', 'S', 'I' , 'A' + (char) id),RTEMS_BARRIER_AUTOMATIC_RELEASE , 10, &(__po_hi_gqueues_barriers[id]));
   if (ret != RTEMS_SUCCESSFUL)
   {
      __PO_HI_DEBUG_WARNING ("[GQUEUE] Cannot create barrier, error code=%d\n", ret);
   }
#endif

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
   __PO_HI_DEBUG_DEBUG ("__po_hi_gqueue_store_out() from task %d on port %d\n", id, port);
}



__po_hi_uint8_t __po_hi_gqueue_store_in (__po_hi_task_id id, 
                                         __po_hi_local_port_t port, 
                                         __po_hi_request_t* request)
{
   __po_hi_request_t* ptr;
#ifdef RTEMS_PURE
   rtems_status_code ret;
#endif
   ptr = &__po_hi_gqueues_most_recent_values[id][port];
#ifdef __PO_HI_DEBUG
   if (ptr == NULL)
   {
      __DEBUGMSG ("__po_hi_gqueue_store_in : NULL POINTER\n");
   }
#endif

#if defined (POSIX) || defined (RTEMS_POSIX)
   pthread_mutex_lock (&__po_hi_gqueues_mutexes[id]);
#elif defined (RTEMS_PURE)
   /*
  ret = rtems_barrier_wait (__po_hi_gqueues_barriers[id], RTEMS_WAIT);

rtems_id                __po_hi_gqueues_semaphores[__PO_HI_NB_TASKS];
rtems_id                __po_hi_gqueues_barriers[__PO_HI_NB_TASKS];
  */
   __DEBUGMSG ("[GQUEUE] Try to obtain semaphore for queue of task %d\n", id);
   ret = rtems_semaphore_obtain (__po_hi_gqueues_semaphores[id], RTEMS_WAIT, RTEMS_NO_TIMEOUT);
   if (ret != RTEMS_SUCCESSFUL)
   {
      __DEBUGMSG ("[GQUEUE] Cannot obtain semaphore in __po_hi_gqueue_store_in()\n");
   }

   __DEBUGMSG ("[GQUEUE] Semaphore got\n");
#endif
   if (__po_hi_gqueues_sizes[id][port] == __PO_HI_GQUEUE_FIFO_INDATA)
   {
      memcpy(ptr,request,sizeof(*request));
   }
   else
   {
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("[GQUEUE] Received  message for task %d, port %d\n", id, port);
#endif
      if (__po_hi_gqueues_used_size[id][port] == __po_hi_gqueues_sizes[id][port])
      {
#if defined (POSIX) || defined (RTEMS_POSIX)
         pthread_mutex_unlock (&__po_hi_gqueues_mutexes[id]);
#elif defined (RTEMS_PURE)
         ret = rtems_semaphore_release (__po_hi_gqueues_semaphores[id]);
         if (ret != RTEMS_SUCCESSFUL)
         {
            __PO_HI_DEBUG_CRITICAL ("[GQUEUE] Cannot release semaphore in __po_hi_gqueue_store_in()\n");
         }
#endif
         __PO_HI_DEBUG_CRITICAL ("[GQUEUE] QUEUE FULL, task-id=%d, port=%d", id, port);
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

#if defined (POSIX) || defined (RTEMS_POSIX)
   pthread_mutex_unlock (&__po_hi_gqueues_mutexes[id]);
   pthread_cond_broadcast (&__po_hi_gqueues_conds[id]);
#elif defined (RTEMS_PURE)
   ret = rtems_semaphore_release (__po_hi_gqueues_semaphores[id]);
   if (ret != RTEMS_SUCCESSFUL)
   {
      __PO_HI_DEBUG_CRITICAL ("[GQUEUE] Cannot release semaphore in __po_hi_gqueue_store_in()\n");
   }
#endif

   return __PO_HI_SUCCESS;
}

void __po_hi_gqueue_wait_for_incoming_event (__po_hi_task_id id, 
                                             __po_hi_local_port_t* port)
{
#ifdef RTEMS_PURE
   rtems_status_code ret;
#endif


#if defined (POSIX) || defined (RTEMS_POSIX)
   pthread_mutex_lock (&__po_hi_gqueues_mutexes[id]);
#elif defined (RTEMS_PURE)
   /*
  ret = rtems_barrier_wait (__po_hi_gqueues_barriers[id], RTEMS_WAIT);

rtems_id                __po_hi_gqueues_semaphores[__PO_HI_NB_TASKS];
rtems_id                __po_hi_gqueues_barriers[__PO_HI_NB_TASKS];
  */
   ret = rtems_semaphore_obtain (__po_hi_gqueues_semaphores[id], RTEMS_WAIT, RTEMS_NO_TIMEOUT);
  if (ret != RTEMS_SUCCESSFUL)
  {
     __DEBUGMSG ("[GQUEUE] Cannot obtain semaphore in __po_hi_gqueue_store_in()\n");
  }
#endif

   while(__po_hi_gqueues_queue_is_empty[id] == 1)
   {
#if defined (POSIX) || defined (RTEMS_POSIX)
      pthread_cond_wait (&__po_hi_gqueues_conds[id],
            &__po_hi_gqueues_mutexes[id]);
#elif defined (RTEMS_PURE)
      ret = rtems_semaphore_release (__po_hi_gqueues_semaphores[id]);
      if (ret != RTEMS_SUCCESSFUL)
      {
         __DEBUGMSG ("[GQUEUE] Cannot obtain semaphore in __po_hi_gqueue_store_in()\n");
      }
      rtems_task_wake_after( RTEMS_YIELD_PROCESSOR );
      ret = rtems_semaphore_obtain (__po_hi_gqueues_semaphores[id], RTEMS_WAIT, RTEMS_NO_TIMEOUT);
      if (ret != RTEMS_SUCCESSFUL)
      {
         __DEBUGMSG ("[GQUEUE] Cannot obtain semaphore in __po_hi_gqueue_store_in()\n");
      }

#endif

   }
   *port = __po_hi_gqueues_global_history[id][__po_hi_gqueues_global_history_offset[id]];
#if defined (POSIX) || defined (RTEMS_POSIX)
   pthread_mutex_unlock (&__po_hi_gqueues_mutexes[id]);
#elif defined (RTEMS_PURE)
   ret = rtems_semaphore_release (__po_hi_gqueues_semaphores[id]);
   if (ret != RTEMS_SUCCESSFUL)
   {
      __DEBUGMSG ("[GQUEUE] Cannot release semaphore in __po_hi_gqueue_store_in()\n");
   }
#endif

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
#ifdef RTEMS_PURE
   rtems_status_code ret;
#endif


   ptr = &__po_hi_gqueues_most_recent_values[id][port];
#if defined (POSIX) || defined (RTEMS_POSIX)
   pthread_mutex_lock (&__po_hi_gqueues_mutexes[id]);
#elif defined (RTEMS_PURE)
   /*
  ret = rtems_barrier_wait (__po_hi_gqueues_barriers[id], RTEMS_WAIT);

rtems_id                __po_hi_gqueues_semaphores[__PO_HI_NB_TASKS];
rtems_id                __po_hi_gqueues_barriers[__PO_HI_NB_TASKS];
  */
   ret = rtems_semaphore_obtain (__po_hi_gqueues_semaphores[id], RTEMS_WAIT, RTEMS_NO_TIMEOUT);
  if (ret != RTEMS_SUCCESSFUL)
  {
     __DEBUGMSG ("[GQUEUE] Cannot obtain semaphore in __po_hi_gqueue_store_in()\n");
  }
#endif


   /*
    * If the port is an event port, with no value queued, then we block
    * the thread.
    */
   if (__po_hi_gqueues_sizes[id][port] != __PO_HI_GQUEUE_FIFO_INDATA)
   {
      while (__po_hi_gqueues_port_is_empty[id][port] == 1)
      {
#if defined (POSIX) || defined (RTEMS_POSIX)
         pthread_cond_wait (&__po_hi_gqueues_conds[id],
               &__po_hi_gqueues_mutexes[id]);
#elif defined (RTEMS_PURE)
         rtems_task_wake_after( RTEMS_YIELD_PROCESSOR );
#endif
      }
   }

   if (__po_hi_gqueues_used_size[id][port] == 0)
   {
      memcpy (request, ptr, sizeof (__po_hi_request_t));
   }
   else
   {
      memcpy (request, 
             (void *)&__po_hi_gqueues[id][port] + ( __po_hi_gqueues_first[id][port] + __po_hi_gqueues_offsets[id][port] )* sizeof (__po_hi_request_t), 
            sizeof (__po_hi_request_t));
   }
    
   
   __PO_HI_DEBUG_INFO ("[GQUEUE] Task %d get a value on port %d\n", id, port);

   /*
    * As this part of the code is now considered as stable, we don't print debug output
    *

   __DEBUGMSG ("RECEIVED vars in gqueue: |");
   {
         int s;
         int i;
         uint8_t* tmp;
         tmp = (unsigned int*) &request->vars;
         s = sizeof (request->vars);
         for (i = 0 ; i < s ; i++)
         {
            printf("%x", *tmp);
            tmp++;
            fflush (stdout);
         }
   }
   __DEBUGMSG ("|\n");
#endif
*/

#if defined (POSIX) || defined (RTEMS_POSIX)
   pthread_mutex_unlock (&__po_hi_gqueues_mutexes[id]);
#elif defined (RTEMS_PURE)
   ret = rtems_semaphore_release (__po_hi_gqueues_semaphores[id]);
   if (ret != RTEMS_SUCCESSFUL)
   {
      __DEBUGMSG ("[GQUEUE] Cannot release semaphore in __po_hi_gqueue_store_in()\n");
   }
#endif

   return 0;
}

int __po_hi_gqueue_next_value (__po_hi_task_id id, __po_hi_local_port_t port)
{
#ifdef RTEMS_PURE
   rtems_status_code ret;
#endif


   /* incomplete semantics, should discriminate and report whether
      there is a next value or not */

   /* XXX change and use assert ? */
   if (__po_hi_gqueues_sizes[id][port] == __PO_HI_GQUEUE_FIFO_INDATA)
   {
      return 1;
   }

#if defined (POSIX) || defined (RTEMS_POSIX)
   pthread_mutex_lock (&__po_hi_gqueues_mutexes[id]);
#elif defined (RTEMS_PURE)
   /*
  ret = rtems_barrier_wait (__po_hi_gqueues_barriers[id], RTEMS_WAIT);

rtems_id                __po_hi_gqueues_semaphores[__PO_HI_NB_TASKS];
rtems_id                __po_hi_gqueues_barriers[__PO_HI_NB_TASKS];
  */
   ret = rtems_semaphore_obtain (__po_hi_gqueues_semaphores[id], RTEMS_WAIT, RTEMS_NO_TIMEOUT);
  if (ret != RTEMS_SUCCESSFUL)
  {
     __DEBUGMSG ("[GQUEUE] Cannot obtain semaphore in __po_hi_gqueue_store_in()\n");
  }
#endif


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

#if defined (POSIX) || defined (RTEMS_POSIX)
   pthread_mutex_unlock (&__po_hi_gqueues_mutexes[id]);
#elif defined (RTEMS_PURE)
   ret = rtems_semaphore_release (__po_hi_gqueues_semaphores[id]);
   if (ret != RTEMS_SUCCESSFUL)
   {
      __DEBUGMSG ("[GQUEUE] Cannot release semaphore in __po_hi_gqueue_store_in()\n");
   }
#endif

   return __PO_HI_SUCCESS;
}

__po_hi_request_t*  __po_hi_gqueue_get_most_recent_value (const __po_hi_task_id task_id, const __po_hi_local_port_t local_port)
{
   return (&__po_hi_gqueues_most_recent_values[task_id][local_port]);
}

uint8_t __po_hi_gqueue_get_destinations_number (const __po_hi_task_id task_id, const __po_hi_local_port_t local_port)
{
      return (__po_hi_gqueues_n_destinations[task_id][local_port]);
}

__po_hi_port_t __po_hi_gqueue_get_destination (const __po_hi_task_id task_id, const __po_hi_local_port_t local_port, const uint8_t destination_number)
{
      return (__po_hi_gqueues_destinations[task_id][local_port][destination_number]);
}

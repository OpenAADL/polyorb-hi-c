/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2018 ESA & ISAE.
 */

#include <po_hi_config.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_transport.h>
#include <po_hi_debug.h>
#include <po_hi_gqueue.h>
#include <po_hi_protected.h>
#include <po_hi_semaphore.h>

#include <po_hi_utils.h>
/* Headers from PolyORB-HI-C */

#include <deployment.h>
#include <activity.h>
#include <request.h>
/* Headers from the generated code */

#include <string.h>
#include <assert.h>
#include <stdlib.h>

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
#include <pthread.h>
#elif defined(__PO_HI_RTEMS_CLASSIC_API)
#include <rtems.h>
#include <inttypes.h>
#include <po_hi_time.h>
#define __PO_HI_DEFAULT_PRIORITY RTEMS_NO_PRIORITY
#elif defined (XENO_NATIVE)
#include <native/cond.h>
#include <native/mutex.h>
#endif

#if defined (MONITORING) /* Headers from run-time verification */
#include <trace_manager.h>
#endif

#define __PO_HI_GQUEUE_OUT_PORT constant_out_identifier
/* give a default value to the out port */

__po_hi_port_t*        __po_hi_gqueues[__PO_HI_NB_TASKS];
__po_hi_port_id_t      __po_hi_gqueues_nb_ports[__PO_HI_NB_TASKS];
__po_hi_port_id_t*     __po_hi_gqueues_sizes[__PO_HI_NB_TASKS];
__po_hi_port_id_t*     __po_hi_gqueues_used_size[__PO_HI_NB_TASKS];
__po_hi_port_id_t*     __po_hi_gqueues_offsets[__PO_HI_NB_TASKS];
__po_hi_port_id_t*     __po_hi_gqueues_woffsets[__PO_HI_NB_TASKS];
__po_hi_port_id_t*     __po_hi_gqueues_n_destinations[__PO_HI_NB_TASKS];
__po_hi_port_t**       __po_hi_gqueues_destinations[__PO_HI_NB_TASKS];
__po_hi_uint32_t       __po_hi_gqueues_total_fifo_size[__PO_HI_NB_TASKS];
__po_hi_request_t*     __po_hi_gqueues_most_recent_values[__PO_HI_NB_TASKS];
__po_hi_port_id_t*     __po_hi_gqueues_first[__PO_HI_NB_TASKS];

__po_hi_port_id_t       __po_hi_gqueues_global_size[__PO_HI_NB_TASKS];
__po_hi_local_port_t*   __po_hi_gqueues_global_history[__PO_HI_NB_TASKS];
__po_hi_uint32_t        __po_hi_gqueues_global_history_offset[__PO_HI_NB_TASKS];
__po_hi_uint32_t        __po_hi_gqueues_global_history_woffset[__PO_HI_NB_TASKS];

__po_hi_port_id_t*       __po_hi_gqueues_port_is_empty[__PO_HI_NB_TASKS];
__po_hi_port_id_t        __po_hi_gqueues_queue_is_empty[__PO_HI_NB_TASKS];
__po_hi_port_id_t        __po_hi_gqueues_n_empty[__PO_HI_NB_TASKS];


__po_hi_sem_t            __po_hi_gqueues_semaphores[__PO_HI_NB_TASKS];



void __po_hi_gqueue_init (__po_hi_task_id       id,
                          __po_hi_port_id_t     nb_ports,
                          __po_hi_port_t        queue[],
                          __po_hi_port_id_t     sizes[],
                          __po_hi_port_id_t     first[],
                          __po_hi_port_id_t     offsets[],
                          __po_hi_port_id_t     woffsets[],
                          __po_hi_port_id_t     n_dest[],
                          __po_hi_port_t*       destinations[],
                          __po_hi_port_id_t     used_size[],
                          __po_hi_local_port_t  history[],
                          __po_hi_request_t     recent[],
                          __po_hi_port_id_t     empties[],
                          __po_hi_uint32_t      total_fifo_size)
{
   __po_hi_port_id_t      tmp;
   __po_hi_uint32_t     off; /* XXX May overflow for large value .. */

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

   __po_hi_gqueues_offsets[id]            = offsets;
   __po_hi_gqueues_n_destinations[id]     = n_dest;
   __po_hi_gqueues_destinations[id]       = destinations;
   __po_hi_gqueues_total_fifo_size[id]    = total_fifo_size;

   __po_hi_gqueues_queue_is_empty[id] = 1;


  /** Using the semaphore API to initialize the semaphore_gqueue array */
  int res = __po_hi_sem_init_gqueue(__po_hi_gqueues_semaphores,id);
  //printf("res dans gqueeu = %d\n", res);
  __DEBUGMSG("GQUEUE_SEM_INIT %d %d\n", id, res);
  assert(res == __PO_HI_SUCCESS);


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
      __po_hi_request_t* request = (__po_hi_request_t*)&__po_hi_gqueues_most_recent_values[id][tmp];
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
   memcpy (ptr, request, sizeof (__po_hi_request_t));
   __PO_HI_DEBUG_DEBUG ("__po_hi_gqueue_store_out() from task %d on port %d\n", id, port);

#if defined (MONITORING)
printf("record_event");
   record_event(ANY, STORE_OUT, id, invalid_port_t, invalid_port_t, port, invalid_local_port_t, request);
#endif

}

__po_hi_port_id_t __po_hi_gqueue_store_in (__po_hi_task_id id,
                                         __po_hi_local_port_t port,
                                         __po_hi_request_t* request)
{
   __po_hi_request_t* ptr;
   __po_hi_request_t* tmp;


   ptr = &__po_hi_gqueues_most_recent_values[id][port];
#ifdef __PO_HI_DEBUG
   if (ptr == NULL)
   {
      __DEBUGMSG ("__po_hi_gqueue_store_in : NULL POINTER\n");
   }
#endif

  /** Locking only a mutex */
  int result = __po_hi_sem_mutex_wait_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_WAIT %d %d\n", id, result);
  assert(result == __PO_HI_SUCCESS);

   if (__po_hi_gqueues_sizes[id][port] == __PO_HI_GQUEUE_FIFO_INDATA)
   {
     memcpy(ptr,request,sizeof(*request));
   }
   else
   {
     __DEBUGMSG ("[GQUEUE] Received  message for task %d, port %d\n", id, port);

      if (__po_hi_gqueues_used_size[id][port] == __po_hi_gqueues_sizes[id][port])
      {
        /** Releasing only a mutex */
        int res = __po_hi_sem_mutex_release_gqueue(__po_hi_gqueues_semaphores,id);
        __DEBUGMSG("GQUEUE_SEM_MTUEX_RELEASE %d %d\n", id, res);
        assert(res == __PO_HI_SUCCESS);

        __PO_HI_DEBUG_CRITICAL ("[GQUEUE] QUEUE FULL, task-id=%d, port=%d\n", id, port);

        __DEBUGMSG ("[GQUEUE] Semaphore released (id=%d)\n", id);
        return __PO_HI_ERROR_QUEUE_FULL;
      }

      __po_hi_uint32_t   size;
      tmp = (__po_hi_request_t*) &__po_hi_gqueues[id][port];
      size = __po_hi_gqueues_woffsets[id][port] + __po_hi_gqueues_first[id][port];

      tmp = tmp + size;

      memcpy (tmp , request, sizeof (__po_hi_request_t));

      __po_hi_gqueues_woffsets[id][port] =  (__po_hi_gqueues_woffsets[id][port] + 1 ) % __po_hi_gqueues_sizes[id][port];

      __po_hi_gqueues_used_size[id][port]++;
      __PO_HI_INSTRUMENTATION_VCD_WRITE("r%d p%d.%d\n", __po_hi_gqueues_used_size[id][port], id, port);

      __po_hi_gqueues_global_history[id][__po_hi_gqueues_global_history_woffset[id]] = port;
      __po_hi_gqueues_global_history_woffset[id] = (__po_hi_gqueues_global_history_woffset[id] + 1 ) % __po_hi_gqueues_total_fifo_size[id];

      if (__po_hi_gqueues_port_is_empty[id][port] == 1)
      {
         __po_hi_gqueues_port_is_empty[id][port] = 0;
         __po_hi_gqueues_n_empty[id]--;
      }
      __po_hi_gqueues_queue_is_empty[id] = 0;
   }
  /** Releasing a semaphore */
  int rel = __po_hi_sem_release_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_RELEASE %d %d\n", id, rel);
  assert(rel == __PO_HI_SUCCESS);

  __DEBUGMSG ("[GQUEUE] store_in completed\n");
  return __PO_HI_SUCCESS;
}


void __po_hi_gqueue_wait_for_incoming_event (__po_hi_task_id id,
                                             __po_hi_local_port_t* port)
{
  /** Locking only the mutex of the semaphore */
  int result = __po_hi_sem_mutex_wait_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_WAIT %d %d\n", id, result);
  assert(result == __PO_HI_SUCCESS);

  while(__po_hi_gqueues_queue_is_empty[id] == 1)
    {
      __PO_HI_INSTRUMENTATION_VCD_WRITE("0t%d\n", id);

    /** Telling the semaphore to wait */
    int res_sem =  __po_hi_sem_wait_gqueue(__po_hi_gqueues_semaphores,id);
    __DEBUGMSG("GQUEUE_SEM_WAIT %d %d\n", id, result);
    assert(res_sem == __PO_HI_SUCCESS);
      __PO_HI_INSTRUMENTATION_VCD_WRITE("1t%d\n", id);
    }

  *port = __po_hi_gqueues_global_history[id][__po_hi_gqueues_global_history_offset[id]];

#if defined (MONITORING)
  printf("record_event");
  record_event(SPORADIC, WAIT_FOR, id, invalid_port_t, invalid_port_t, *port, invalid_local_port_t, NULL);
#endif

  /** Releasing only the mutex of the semaphore*/
  int res = __po_hi_sem_mutex_release_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MTUEX_RELEASE %d %d\n", id, res);
  assert(res == __PO_HI_SUCCESS);

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


int __po_hi_gqueue_get_value (__po_hi_task_id      id,
                              __po_hi_local_port_t port,
                              __po_hi_request_t*   request)
{
   __po_hi_request_t* ptr;
#ifdef __PO_HI_RTEMS_CLASSIC_API
   rtems_status_code ret;
#endif

#ifdef _WIN32
   DWORD ret;
#endif

   ptr = &__po_hi_gqueues_most_recent_values[id][port];

 /** Locking only the mutex of the semaphore */
  int result = __po_hi_sem_mutex_wait_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_WAIT %d %d\n", id, result);
  assert(result == __PO_HI_SUCCESS);

   /*
    * If the port is an event port, with no value queued, then we block
    * the thread.
    */
   if (__po_hi_gqueues_sizes[id][port] != __PO_HI_GQUEUE_FIFO_INDATA)
   {
      while (__po_hi_gqueues_port_is_empty[id][port] == 1)
      {
        /** Telling the semaphore to wait */
        int res_sem =  __po_hi_sem_wait_gqueue(__po_hi_gqueues_semaphores,id);
        __DEBUGMSG("GQUEUE_SEM_WAIT %d %d\n", id, result);
        assert(res_sem == __PO_HI_SUCCESS);
      }
   }

#if defined (MONITORING)
printf("record_event");
   record_event(ANY, GET_VALUE, id, invalid_port_t, invalid_port_t, port, invalid_local_port_t , request);
#endif

   if (__po_hi_gqueues_used_size[id][port] == 0)
   {
      memcpy (request, ptr, sizeof (__po_hi_request_t));
      //update_runtime (id, port, ptr);
   }
   else
   {
      ptr = ((__po_hi_request_t *) &__po_hi_gqueues[id][port]) +  __po_hi_gqueues_first[id][port] + __po_hi_gqueues_offsets[id][port];
      memcpy (request, ptr, sizeof (__po_hi_request_t));
   }

   __PO_HI_DEBUG_INFO ("[GQUEUE] Task %d get a value on port %d\n", id, port);

/** Releasing only the mutex of the semaphore*/
  int res = __po_hi_sem_mutex_release_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_RELEASE %d %d\n", id, res);
  assert(res == __PO_HI_SUCCESS);

   return 0;
}

int __po_hi_gqueue_next_value (__po_hi_task_id id, __po_hi_local_port_t port)
{
#ifdef __PO_HI_RTEMS_CLASSIC_API
   rtems_status_code ret;
#endif

   /* incomplete semantics, should discriminate and report whether
      there is a next value or not */

   /* XXX change and use assert ? */
   if (__po_hi_gqueues_sizes[id][port] == __PO_HI_GQUEUE_FIFO_INDATA)
   {
      return 1;
   }

 /** Locking a mutex */
  int result = __po_hi_sem_mutex_wait_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_WAIT %d %d\n", id, result);
  assert(result == __PO_HI_SUCCESS);

   __po_hi_gqueues_offsets[id][port] =
      (__po_hi_gqueues_offsets[id][port] + 1)
      % __po_hi_gqueues_sizes[id][port];

   __po_hi_gqueues_used_size[id][port]--;

   __PO_HI_INSTRUMENTATION_VCD_WRITE("r%d p%d.%d\n", __po_hi_gqueues_used_size[id][port], id, port);

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


/** Releasing a mutex*/
  int res = __po_hi_sem_mutex_release_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_RELEASE %d %d\n", id, res);
  assert(res == __PO_HI_SUCCESS);

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

__po_hi_port_id_t __po_hi_gqueue_get_port_size( __po_hi_task_id id, __po_hi_local_port_t port)
{
   return __po_hi_gqueues_sizes[id][port];
}

__po_hi_port_id_t __po_hi_gqueue_used_size( __po_hi_task_id id, __po_hi_local_port_t port)
{
   return __po_hi_gqueues_used_size[id][port];
}

__po_hi_port_id_t po_hi_gqueues_queue_is_empty( __po_hi_task_id id)
{
   return __po_hi_gqueues_queue_is_empty[id];
}

__po_hi_request_t*
__po_hi_gqueues_get_request(__po_hi_task_id id, __po_hi_local_port_t port)

 {
  __po_hi_request_t* request ;
  __po_hi_request_t* ptr ;
  request = calloc(1,sizeof(__po_hi_request_t));
  ptr = &__po_hi_gqueues_most_recent_values[id][port];
   if (__po_hi_gqueues_used_size[id][port] == 0)
   {
      memcpy (request, ptr, sizeof (__po_hi_request_t));
      //update_runtime (id, port, ptr);
   }
   else
   {
      ptr = ((__po_hi_request_t *) &__po_hi_gqueues[id][port]) +  __po_hi_gqueues_first[id][port] + __po_hi_gqueues_offsets[id][port];
      memcpy (request, ptr, sizeof (__po_hi_request_t));
   }	return request;
}

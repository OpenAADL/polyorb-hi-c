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

/**
 * The following macro may be defined to add runtime assertions and debug for the gqueue
 */
/* #define __PO_HI_GQUEUE_ASSERTIONS */

/**
 * Pointer Array containing the whole gqueue.
 * The gqueue is divided in multiple gqueues : by task then for each task by ports.
 */
__po_hi_request_t*     __po_hi_gqueues[__PO_HI_NB_TASKS];

/**
 * Array showing the number of ports for each tasks.
 */
__po_hi_port_id_t      __po_hi_gqueues_nb_ports[__PO_HI_NB_TASKS];

/**
 * Array showing the size of the FIFO for each port of each task, or
 * __PO_HI_GQUEUE_FIFO_OUT if this is an out port.
 */
__po_hi_port_id_t*     __po_hi_gqueues_sizes[__PO_HI_NB_TASKS];

/**
 * Array showing the effective size used for each port (for each task).
 */
__po_hi_port_id_t*     __po_hi_gqueues_used_size[__PO_HI_NB_TASKS];

/**
 * Array showing the offset necessary to add from the beginning of a
 * port gqueue to access the part allowed to reading.  When adding
 * that offset to the beginning of the PORT gqueue, you enter the part
 * of the port gqueue in which the read value get input.
 */
__po_hi_port_id_t*     __po_hi_gqueues_offsets[__PO_HI_NB_TASKS];

/**
 * Array showing the offset necessary to add from the beginning of a
 * port gqueue to access the part allowed to writing.  When adding
 * that offset to the beginning of the PORT gqueue, you enter the part
 * of the port gqueue in which the written value get input.
 */
__po_hi_port_id_t*     __po_hi_gqueues_woffsets[__PO_HI_NB_TASKS];

/**
 * Array showing the number of destinations for each port.
 */
__po_hi_port_id_t*     __po_hi_gqueues_n_destinations[__PO_HI_NB_TASKS];

/**
 * Array showing the destination for each port.
 */
__po_hi_port_t**       __po_hi_gqueues_destinations[__PO_HI_NB_TASKS];

/**
 * Array showing the size of the FIFO gqueue for each task
 * (subdivision by tasks of the whole gqueue).
 */
__po_hi_uint32_t       __po_hi_gqueues_total_fifo_size[__PO_HI_NB_TASKS];

/**
 * Array showing the most recent value added (for each port of each task).
 */
__po_hi_request_t*     __po_hi_gqueues_most_recent_values[__PO_HI_NB_TASKS];

/**
 * Array showing the offset necessary to add from the beginning of a
 * task gqueue to access a specified port gqueue.  When adding that
 * offset to the beginning of the TASK gqueue, you enter the beginning
 * of the port gqueue.
 */
__po_hi_port_id_t*     __po_hi_gqueues_first[__PO_HI_NB_TASKS];

/**
 * Unused.
 */
__po_hi_port_id_t      __po_hi_gqueues_global_size[__PO_HI_NB_TASKS];

/**
 * Array helping in managing the offsets and woffsets in integers.
 */
__po_hi_local_port_t*  __po_hi_gqueues_global_history[__PO_HI_NB_TASKS];

/**
 * Array in managing the offsets in integers.
 */
__po_hi_uint32_t        __po_hi_gqueues_global_history_offset[__PO_HI_NB_TASKS];

/**
 * Array in managing the woffsets in integers.
 */
__po_hi_uint32_t       __po_hi_gqueues_global_history_woffset[__PO_HI_NB_TASKS];

/**
 * Array showing whether the queue of a specified port of a task is empty (1) or not (0).
 */
__po_hi_port_id_t*     __po_hi_gqueues_port_is_empty[__PO_HI_NB_TASKS];

/**
 * Array showing whether the global queue of a task is empty (1) or not (0).
 */
__po_hi_port_id_t      __po_hi_gqueues_queue_is_empty[__PO_HI_NB_TASKS];

/**
 * Array counting how many ports gqueue of a specified task are empty.
 * If the number of empty ports (n_empty) is equal to the number of
 * ports (nb_ports), then the queue is declared empty in the array
 * __po_hi_gqueues_queue_is_empty.
 */
__po_hi_port_id_t      __po_hi_gqueues_n_empty[__PO_HI_NB_TASKS];

/**
 * Array containing the semaphores for each tasks.
 */
__po_hi_sem_t          __po_hi_gqueues_semaphores[__PO_HI_NB_TASKS];

/******************************************************************************/
void __po_hi_gqueue_init (__po_hi_task_id       id,
                          __po_hi_port_id_t     nb_ports,
                          __po_hi_request_t     queue[],
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
  __po_hi_port_id_t    tmp;
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

  /* Using the semaphore API to initialize the semaphore_gqueue array */
  int res = __po_hi_sem_init_gqueue(__po_hi_gqueues_semaphores,id);
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

  __PO_HI_DEBUG_DEBUG("Initialize global queue for task %d , first = %d, history_offset = %d, history_woffset = %d, fifo size = %d, gqueue_id adress = %d\n\n", id, __po_hi_gqueues_first[id],__po_hi_gqueues_global_history_offset[id],__po_hi_gqueues_global_history_woffset[id], __po_hi_gqueues_total_fifo_size[id],__po_hi_gqueues[id] );

#if defined __PO_HI_GQUEUE_ASSERTIONS
  __DEBUGMSG("\nInitialization parameter");
  assert(__po_hi_gqueues_global_history_woffset[id] == 0);
  assert(__po_hi_gqueues_global_history_offset[id] == 0);
  assert(__po_hi_gqueues_n_empty[id] == nb_ports);
  assert(__po_hi_gqueues[id] == queue);
  assert(__po_hi_gqueues_most_recent_values[id] == recent);
  assert(__po_hi_gqueues_global_history[id] == history);
  assert(__po_hi_gqueues_woffsets[id] == woffsets);
  assert(__po_hi_gqueues_port_is_empty[id] == empties);
  assert(__po_hi_gqueues_nb_ports[id] == nb_ports);
  assert(__po_hi_gqueues_sizes[id] == sizes);
  assert(__po_hi_gqueues_first[id] == first);
  assert(__po_hi_gqueues_used_size[id] == used_size);
  assert(__po_hi_gqueues_offsets[id]           == offsets);
  assert(__po_hi_gqueues_n_destinations[id]    == n_dest);
  assert(__po_hi_gqueues_destinations[id]      == destinations);
  assert(__po_hi_gqueues_total_fifo_size[id]   == total_fifo_size);
  assert(__po_hi_gqueues_queue_is_empty[id] = 1);

  for (__po_hi_port_id_t i = 0; i < nb_ports; i++){
    assert(__po_hi_gqueues_used_size[id][i] == 0);
    assert(__po_hi_gqueues_most_recent_values[id][i].port == __PO_HI_GQUEUE_INVALID_PORT);
    if (i > 0){
      /* Usually HAS TO be right */
      //assert(__po_hi_gqueues_first[id][i] >= 0);
    }
  }
#endif
}

/******************************************************************************/
void __po_hi_gqueue_store_out (__po_hi_task_id id,
                               __po_hi_local_port_t port,
                               __po_hi_request_t* request)
{
  __po_hi_request_t* ptr;

  request->port = __PO_HI_GQUEUE_OUT_PORT;
  ptr = &__po_hi_gqueues_most_recent_values[id][port];
  memcpy (ptr, request, sizeof (__po_hi_request_t));
  __PO_HI_DEBUG_DEBUG ("\n__Po_hi_gqueue_store_out() from task %d on port %d\n", id, port);

#if defined (MONITORING)
  __DEBUGMSG("\nThe last value is the request to be stored");
  record_event(ANY, STORE_OUT, id, invalid_port_t, invalid_port_t, port, invalid_local_port_t, request);
#endif

}

/******************************************************************************/
__po_hi_port_id_t __po_hi_gqueue_store_in (__po_hi_task_id id,
                                           __po_hi_local_port_t port,
                                           __po_hi_request_t* request)
{

#ifdef __PO_HI_GQUEUE_ASSERTIONS
  __po_hi_port_id_t init_woffset         = __po_hi_gqueues_woffsets[id][port];
  __po_hi_uint32_t  init_history_woffset = __po_hi_gqueues_global_history_woffset[id];
  __po_hi_port_id_t init_used_size       = __po_hi_gqueues_used_size[id][port];
  __po_hi_port_id_t is_empty             = __po_hi_gqueues_port_is_empty[id][port];
  __po_hi_port_id_t nb_empty             =  __po_hi_gqueues_n_empty[id];
#endif

  __po_hi_request_t* ptr;
  __po_hi_request_t* tmp;

  ptr = &__po_hi_gqueues_most_recent_values[id][port];
#ifdef __PO_HI_DEBUG
  if (ptr == NULL)
    {
      __DEBUGMSG ("__po_hi_gqueue_store_in : NULL POINTER\n");
    }
#endif
  /* Locking only a mutex */
  __PO_HI_DEBUG_DEBUG ("\nWaiting on Store_in on task %d, port = %d, size of port = %d\n", id, port,__po_hi_gqueue_get_port_size(id, port));
  int result = __po_hi_sem_mutex_wait_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_WAIT on task %d result = %d\n", id, result);
  assert(result == __PO_HI_SUCCESS);

  if (__po_hi_gqueue_get_port_size(id,port) == __PO_HI_GQUEUE_FIFO_INDATA)
    {
      memcpy(ptr,request,sizeof(*request));
      __PO_HI_DEBUG_CRITICAL ("[GQUEUE] BEWARE, for a FIFO_INDATA port, the used_size is always at 0 (not augmented in a store_in) task-id=%d, port=%d\n", id, port);
    }
  else
    {
      __DEBUGMSG ("[GQUEUE] Received  message for task %d, port %d\n", id, port);

      if (__po_hi_gqueue_used_size(id,port) == __po_hi_gqueue_get_port_size(id,port))
        {
          /* Releasing only a mutex */
          int res = __po_hi_sem_mutex_release_gqueue(__po_hi_gqueues_semaphores,id);
          __DEBUGMSG("GQUEUE_SEM_MTUEX_RELEASE %d %d\n", id, res);
          assert(res == __PO_HI_SUCCESS);

          __PO_HI_DEBUG_CRITICAL ("[GQUEUE] QUEUE FULL, task-id=%d, port=%d\n", id, port);

          __DEBUGMSG ("[GQUEUE] Semaphore released (id=%d)\n", id);
          return __PO_HI_ERROR_QUEUE_FULL;
        }

      __PO_HI_DEBUG_DEBUG("\nBefore store_in for task-id %d , port %d, offset = %d, woffset = %d, history_offset = %d, history_woffset = %d, port size = %d, fifo size = %d, gqueue id adress = %d,\n\n", id, port, __po_hi_gqueues_offsets[id][port], __po_hi_gqueues_woffsets[id][port],__po_hi_gqueues_global_history_offset[id],__po_hi_gqueues_global_history_woffset[id], __po_hi_gqueues_sizes[id][port], __po_hi_gqueues_total_fifo_size[id], __po_hi_gqueues[id]);

      /* The program ensures to write the information at the right place in the buffer.
       *
       * The right first offset has to be applied so that the right
       * port is chosen.  The right woffset (writing_offset) has to be
       * applied not to erase fresh information.
       */
      __po_hi_uint32_t   size;
      tmp =  __po_hi_gqueues[id];
      size = __po_hi_gqueues_woffsets[id][port] + __po_hi_gqueues_first[id][port];

      tmp = tmp + size;
      __PO_HI_DEBUG_DEBUG(" Store_in first + woffsets = %d, first = %d, gqueue_id adress = %d, tmp (adress + woffset + first)= %d,\n\n", __po_hi_gqueues_first[id][port] + __po_hi_gqueues_woffsets[id][port],__po_hi_gqueues_first[id][port],__po_hi_gqueues[id], tmp);

      memcpy (tmp , request, sizeof (__po_hi_request_t));

      __po_hi_gqueues_woffsets[id][port] = (__po_hi_gqueues_woffsets[id][port] + 1 ) % __po_hi_gqueues_sizes[id][port];
      __PO_HI_DEBUG_DEBUG ("\nBefore used_size ++, Store_in for task = %d, __po_hi_gqueues_used_size[id][port] = %d\n", id, __po_hi_gqueues_used_size[id][port]);
      __po_hi_gqueues_used_size[id][port]++;
      __PO_HI_DEBUG_DEBUG ("\nAfter used_size ++ , Store_in for task = %d, __po_hi_gqueues_used_size[id][port] = %d\n",id,  __po_hi_gqueues_used_size[id][port]);
      __PO_HI_INSTRUMENTATION_VCD_WRITE("r%d p%d.%d\n", __po_hi_gqueue_used_size(id,port), id, port);

      /* The port where information has been written is stored */
      __po_hi_gqueues_global_history[id][__po_hi_gqueues_global_history_woffset[id]] = port;
      __po_hi_gqueues_global_history_woffset[id] = (__po_hi_gqueues_global_history_woffset[id] + 1 ) % __po_hi_gqueues_total_fifo_size[id];

      if (__po_hi_gqueues_port_is_empty[id][port] == 1)
        {
          __po_hi_gqueues_port_is_empty[id][port] = 0;
          __po_hi_gqueues_n_empty[id]--;
        }
      __po_hi_gqueues_queue_is_empty[id] = 0;
    }

  __PO_HI_DEBUG_DEBUG("\nAfter store_in for task-id %d , port %d, offset = %d, woffset = %d, history_offset = %d, history_woffset = %d, port size = %d, fifo size = %d, gqueue_id adress= %d, \n\n", id, port,  __po_hi_gqueues_offsets[id][port], __po_hi_gqueues_woffsets[id][port],__po_hi_gqueues_global_history_offset[id],__po_hi_gqueues_global_history_woffset[id], __po_hi_gqueues_sizes[id][port], __po_hi_gqueues_total_fifo_size[id], __po_hi_gqueues[id]);

  /* Releasing a complete semaphore */
  int rel = __po_hi_sem_release_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_RELEASE %d %d\n", id, rel);
  assert(rel == __PO_HI_SUCCESS);
  __DEBUGMSG ("[GQUEUE] store_in completed\n");

#ifdef __PO_HI_GQUEUE_ASSERTIONS
  /* The port length is superior to 1 */
  if ((__po_hi_gqueue_get_port_size(id,port) != __PO_HI_GQUEUE_FIFO_INDATA)&&(init_used_size != __po_hi_gqueue_get_port_size(id,port))){
    __DEBUGMSG("\nThe woffset should be incremented by one and stay inferior to the port size");
    assert(__po_hi_gqueues_woffsets[id][port] == (init_woffset + 1)% __po_hi_gqueues_sizes[id][port]);
    assert(__po_hi_gqueues_woffsets[id][port] < __po_hi_gqueues_sizes[id][port]);
    __DEBUGMSG("\nThe effective port size used should be incremented by one");
    assert (__po_hi_gqueues_used_size[id][port] == init_used_size +1);
    __DEBUGMSG("\nThe port array is filled by the right port so that the reading is done at the right port");
    assert (__po_hi_gqueues_global_history[id][init_history_woffset] == port);
    __DEBUGMSG("The woffset_index should then be incremented by one and stay inferior to the fifo size");
    assert(__po_hi_gqueues_global_history_woffset[id] == (init_history_woffset + 1)% __po_hi_gqueues_total_fifo_size[id]);
    assert(__po_hi_gqueues_global_history_woffset[id] < __po_hi_gqueues_total_fifo_size[id]);
    __DEBUGMSG("\nIf this port queue was empty, the number of empty port is reduced by 1");
    /* The port was empty */
    if (is_empty == 1){
      assert(__po_hi_gqueues_n_empty[id] == nb_empty - 1);
    }
    __DEBUGMSG("\nThis port queue must be considered not empty ");
    assert (__po_hi_gqueues_port_is_empty[id][port] == 0);
    __DEBUGMSG("\nThe task queue must be considered not empty ");
    assert (__po_hi_gqueues_queue_is_empty[id] == 0);
  }
#endif

  return __PO_HI_SUCCESS;
}

/******************************************************************************/
void __po_hi_gqueue_wait_for_incoming_event (__po_hi_task_id id,
                                             __po_hi_local_port_t* port)
{
  /* Locking only the mutex of the semaphore */
  int result = __po_hi_sem_mutex_wait_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_WAIT %d %d\n", id, result);
  assert(result == __PO_HI_SUCCESS);

  while(po_hi_gqueues_queue_is_empty(id) == 1)
    {
      __PO_HI_INSTRUMENTATION_VCD_WRITE("0t%d\n", id);

      /* Telling the semaphore to wait with putting its condvar on wait mode */
      int res_sem =  __po_hi_sem_wait_gqueue(__po_hi_gqueues_semaphores,id);
      __DEBUGMSG("GQUEUE_SEM_WAIT %d %d\n", id, res_sem);
      assert(res_sem == __PO_HI_SUCCESS);
      __PO_HI_INSTRUMENTATION_VCD_WRITE("1t%d\n", id);
    }

  *port = __po_hi_gqueues_global_history[id][__po_hi_gqueues_global_history_offset[id]];

#if defined (MONITORING)
  record_event(SPORADIC, WAIT_FOR, id, invalid_port_t, invalid_port_t, *port, invalid_local_port_t, NULL);
#endif

  /** Releasing only the mutex of the semaphore*/

  int res = __po_hi_sem_mutex_release_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MTUEX_RELEASE %d %d\n", id, res);
  assert(res == __PO_HI_SUCCESS);

#ifdef __PO_HI_GQUEUE_ASSERTIONS
  __DEBUGMSG("\nThe task queue must be considered not empty ");
  assert (*port == __po_hi_gqueues_global_history[id][__po_hi_gqueues_global_history_offset[id]]);
#endif
}

/******************************************************************************/
int __po_hi_gqueue_get_count( __po_hi_task_id id, __po_hi_local_port_t port)
{
  if (__po_hi_gqueue_get_port_size(id,port) == __PO_HI_GQUEUE_FIFO_INDATA)
    {
      __PO_HI_DEBUG_CRITICAL ("[GQUEUE] BEWARE a FIFO_INDATA port will always have a get_count of 1, even if empty, task-id=%d, port=%d\n", id, port);
      return 1; /* data port are always of size 1 */
    }
  else
    {
      return (__po_hi_gqueue_used_size(id,port));
    }
}

/******************************************************************************/
int __po_hi_gqueue_get_value (__po_hi_task_id      id,
                              __po_hi_local_port_t port,
                              __po_hi_request_t*   request)
{
  __po_hi_request_t* ptr;

  __PO_HI_DEBUG_DEBUG("before get_value for task-id %d , port = %d, offset = %d, woffset = %d, history_offset = %d, history_woffset = %d, port size = %d , fifo size = %d, gqueues_id adress = %d, \n\n", id, port, __po_hi_gqueues_offsets[id][port], __po_hi_gqueues_woffsets[id][port],__po_hi_gqueues_global_history_offset[id],__po_hi_gqueues_global_history_woffset[id], __po_hi_gqueues_sizes[id][port], __po_hi_gqueues_total_fifo_size[id], __po_hi_gqueues[id]);

  ptr = &__po_hi_gqueues_most_recent_values[id][port];

  /* Locking only the mutex of the semaphore */
  int result = __po_hi_sem_mutex_wait_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_WAIT %d %d\n", id, result);
  assert(result == __PO_HI_SUCCESS);

  /*
   * If the port is an OUTPUT, with no value queued, the function returns
   * nothing.
   */
  if (__po_hi_gqueue_get_port_size(id,port) == -2)
    {
      __PO_HI_DEBUG_CRITICAL ("[GQUEUE] OUTPUT PORT, REQUEST NOT SET UP, task-id=%d, port=%d\n", id, port);
      __DEBUGMSG("THE PORT IS AN OUTPUT, REQUEST NOT SET UP");
        /* Releasing only the mutex of the semaphore*/
       int rel = __po_hi_sem_mutex_release_gqueue(__po_hi_gqueues_semaphores,id);
       __DEBUGMSG("GQUEUE_SEM_MUTEX_RELEASE %d %d\n", id, rel);
       assert(rel == __PO_HI_SUCCESS);
      return __PO_HI_INVALID;
    }
  /*
   * If the port is an event port, with no value queued, then we block
   * the thread.
   */
  /* Empty port case 1 : NO FIFO INDATA */
  if (__po_hi_gqueue_get_port_size(id,port) != __PO_HI_GQUEUE_FIFO_INDATA)
    {
      while (__po_hi_gqueues_port_is_empty[id][port] == 1)
        {
          /* Telling the semaphore to wait with putting its condvar on wait mode */
          int res_sem =  __po_hi_sem_wait_gqueue(__po_hi_gqueues_semaphores,id);
          __DEBUGMSG("GQUEUE_SEM_WAIT %d %d\n", id, result);
          assert(res_sem == __PO_HI_SUCCESS);
        }
    }
  /* Empty port case 2 : FIFO INDATA */
  if ((__po_hi_gqueue_get_port_size(id,port) == __PO_HI_GQUEUE_FIFO_INDATA) && (__po_hi_gqueue_used_size(id,port) == 0))
    {
      memcpy (request, ptr, sizeof (__po_hi_request_t));
      //update_runtime (id, port, ptr);
    }
  else
    {
      /* The program ensures to read the information at the right place in the buffer.
       * The right first offset has to be applied so that the right port is chosen.
       * The right offset (read_offset) has to be applied not to erase fresh information.
       */

      ptr = (__po_hi_gqueues[id]) +  __po_hi_gqueues_first[id][port] + __po_hi_gqueues_offsets[id][port];
      __PO_HI_DEBUG_DEBUG("Get_value if port not empty first + offsets = %d, gqueue_id adress =  %d, first = %d, ptr (adress + first +offset) = %d, \n\n",  __po_hi_gqueues_first[id][port] + __po_hi_gqueues_offsets[id][port],__po_hi_gqueues[id], __po_hi_gqueues_first[id][port], ptr);
      memcpy (request, ptr, sizeof (__po_hi_request_t));
    }

#if defined (MONITORING)
  record_event(ANY, GET_VALUE, id, invalid_port_t, invalid_port_t, port, invalid_local_port_t , request);
#endif

  __PO_HI_DEBUG_INFO ("[GQUEUE] Task %d get a value on port %d\n", id, port);

  /* Releasing only the mutex of the semaphore*/
  int res = __po_hi_sem_mutex_release_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_RELEASE %d %d\n", id, res);
  assert(res == __PO_HI_SUCCESS);

  __PO_HI_DEBUG_DEBUG("After get_value for task-id %d , port = %d, offset = %d, woffset = %d, history_offset = %d, history_woffset = %d, port size = %d, fifo size = %d, gqueues adress = %d \n\n", id, port, __po_hi_gqueues_offsets[id][port], __po_hi_gqueues_woffsets[id][port],__po_hi_gqueues_global_history_offset[id],__po_hi_gqueues_global_history_woffset[id], __po_hi_gqueues_sizes[id][port], __po_hi_gqueues_total_fifo_size[id], __po_hi_gqueues[id]);
  return __PO_HI_SUCCESS;
}

/******************************************************************************/
int __po_hi_gqueue_next_value (__po_hi_task_id id, __po_hi_local_port_t port)
{

#ifdef __PO_HI_GQUEUE_ASSERTIONS
  __po_hi_port_id_t init_offset = __po_hi_gqueues_offsets[id][port];
  __po_hi_uint32_t init_history_offset = __po_hi_gqueues_global_history_offset[id];
  __po_hi_port_id_t init_used_size = __po_hi_gqueues_used_size[id][port];
  __po_hi_port_id_t nb_empty =  __po_hi_gqueues_n_empty[id];
#endif

  /* Incomplete semantics, Should discriminate and report whether
     there is a next value or not */
  if (__po_hi_gqueue_get_port_size(id,port) == __PO_HI_GQUEUE_FIFO_INDATA)
    {
      __PO_HI_DEBUG_CRITICAL ("[GQUEUE] BEWARE, for a FIFO_INDATA port, the used_size is always at 0 (not reduced in a next_value) task-id=%d, port=%d\n", id, port);
      return 1;
    }

  /* Locking a mutex */
  __PO_HI_DEBUG_DEBUG ("\nWaiting on next_value on task %d, port = %d, size of port = %d\n", id, port,__po_hi_gqueue_get_port_size(id, port));
  int result = __po_hi_sem_mutex_wait_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_WAIT %d %d\n", id, result);
  assert(result == __PO_HI_SUCCESS);

  __PO_HI_DEBUG_DEBUG("\nBefore next_value for task-id %d , offset = %d, woffset = %d, history_offset = %d, history_woffset = %d, port_size = %d, fifo size = %d, gqueues adress = %d, \n\n", id, __po_hi_gqueues_offsets[id][port], __po_hi_gqueues_woffsets[id][port],__po_hi_gqueues_global_history_offset[id],__po_hi_gqueues_global_history_woffset[id], __po_hi_gqueues_sizes[id][port], __po_hi_gqueues_total_fifo_size[id], __po_hi_gqueues[id]);

  __po_hi_gqueues_offsets[id][port] =
    (__po_hi_gqueues_offsets[id][port] + 1)
    % __po_hi_gqueues_sizes[id][port];
  __PO_HI_DEBUG_DEBUG ("\nBefore -- on size, Next_value for task id = %d, __po_hi_gqueues_used_size[id][port] = %d\n",id, __po_hi_gqueues_used_size[id][port]);
  __po_hi_gqueues_used_size[id][port]--;
  __PO_HI_DEBUG_DEBUG ("\nAfter -- on size , Next_value for task id = %d, __po_hi_gqueues_used_size[id][port] = %d\n",id, __po_hi_gqueues_used_size[id][port]);
  __PO_HI_INSTRUMENTATION_VCD_WRITE("r%d p%d.%d\n", __po_hi_gqueue_used_size(id,port), id, port);

  if (__po_hi_gqueue_used_size(id,port) == 0)
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

  __PO_HI_DEBUG_DEBUG("\nAfter next_value for task-id %d , offset = %d, woffset = %d, history_offset = %d, history_woffset = %d , port size = %d, fifo size = %d, gqueue = %d \n\n", id, __po_hi_gqueues_offsets[id][port], __po_hi_gqueues_woffsets[id][port],__po_hi_gqueues_global_history_offset[id],__po_hi_gqueues_global_history_woffset[id], __po_hi_gqueues_sizes[id][port], __po_hi_gqueues_total_fifo_size[id], __po_hi_gqueues[id]);

  /* Releasing a mutex*/
  int res = __po_hi_sem_mutex_release_gqueue(__po_hi_gqueues_semaphores,id);
  __DEBUGMSG("GQUEUE_SEM_MUTEX_RELEASE %d %d\n", id, res);
  assert(res == __PO_HI_SUCCESS);

#ifdef __PO_HI_GQUEUE_ASSERTIONS
  /* The port length is superior to 1 */
  if ((__po_hi_gqueue_get_port_size(id,port) != __PO_HI_GQUEUE_FIFO_INDATA)){
    __DEBUGMSG("\nThe woffset should be incremented by one");
    assert(__po_hi_gqueues_offsets[id][port] == (init_offset + 1)% __po_hi_gqueues_sizes[id][port]);
    assert(__po_hi_gqueues_offsets[id][port] < __po_hi_gqueues_sizes[id][port]);
    __DEBUGMSG("\nThe effective port size used should be decremented by one");
    assert (__po_hi_gqueues_used_size[id][port] == init_used_size -1);
    __DEBUGMSG("The offset_index should then be incremented by one");
    assert(__po_hi_gqueues_global_history_offset[id] == (init_history_offset + 1)% __po_hi_gqueues_total_fifo_size[id]);
    assert(__po_hi_gqueues_global_history_offset[id] < __po_hi_gqueues_total_fifo_size[id]);
    __DEBUGMSG("\nIf this port queue was empty, the number of empty port is reduced by 1");
    /* If the port is now empty */
    if (__po_hi_gqueue_used_size(id,port) == 0){
      assert(__po_hi_gqueues_n_empty[id] == nb_empty + 1);
      __DEBUGMSG("\nThis port queue must be considered empty ");
      assert(__po_hi_gqueues_port_is_empty[id][port] == 1);
    }
    if (__po_hi_gqueues_n_empty[id] == __po_hi_gqueues_nb_ports[id])
      {
        assert(__po_hi_gqueues_queue_is_empty[id] == 1);
      }
  }
#endif
  return __PO_HI_SUCCESS;
}

/******************************************************************************/
__po_hi_request_t*  __po_hi_gqueue_get_most_recent_value (__po_hi_task_id task_id,
                                                          __po_hi_local_port_t local_port)
{
  return (&__po_hi_gqueues_most_recent_values[task_id][local_port]);
}

/******************************************************************************/
__po_hi_port_id_t __po_hi_gqueue_get_destinations_number (__po_hi_task_id task_id,
                                                          __po_hi_local_port_t local_port)
{
  return (__po_hi_gqueues_n_destinations[task_id][local_port]);
}

/******************************************************************************/
__po_hi_port_t __po_hi_gqueue_get_destination (__po_hi_task_id task_id,
                                               __po_hi_local_port_t local_port,
                                               uint8_t destination_number)
{
  return (__po_hi_gqueues_destinations[task_id][local_port][destination_number]);
}

/******************************************************************************/
__po_hi_port_id_t __po_hi_gqueue_get_port_size(__po_hi_task_id id,
                                               __po_hi_local_port_t port)
{
  return __po_hi_gqueues_sizes[id][port];
}

/******************************************************************************/
__po_hi_port_id_t __po_hi_gqueue_used_size(__po_hi_task_id id,
                                           __po_hi_local_port_t port)
{
  return __po_hi_gqueues_used_size[id][port];
}

/******************************************************************************/
__po_hi_port_id_t po_hi_gqueues_queue_is_empty( __po_hi_task_id id)
{
  return __po_hi_gqueues_queue_is_empty[id];
}

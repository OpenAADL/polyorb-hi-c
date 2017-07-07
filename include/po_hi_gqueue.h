/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2017 ESA & ISAE.
 */

#ifndef __PO_HI_GQUEUE_H__
#define __PO_HI_GQUEUE_H__

#define __PO_HI_GQUEUE_FULL      10

#define __PO_HI_GQUEUE_FIFO_INDATA    -1
#define __PO_HI_GQUEUE_FIFO_OUT       -2

#define __PO_HI_GQUEUE_INVALID_PORT invalid_port_t
#define __PO_HI_GQUEUE_INVALID_LOCAL_PORT invalid_local_port_t

#include <deployment.h>
#include <request.h>
#include <po_hi_types.h>

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
			  __po_hi_uint32_t      total_fifo_size);
/*
 * Initialize a global queue. In a distributed system, each task has
 * its own global queue. This function is invoked by each thead to
 * create its global queue, according to its information (number of
 * ports, destination of each port ...).
 *
 * The first argument is the task-id in the distributed system. The
 * second argument is the number of ports for the task. The argument
 * sizes contains the size of the FIFO for each port. The offsets
 * argument contains the offset position for each queue in the global
 * queue.  The n_dest argument correspond to the number of
 * destinations for an OUT port. The argument destinations tells what
 * are the ports connected to an OUT port.  Finally, the argument
 * total_fifo_size gives the total size of the global queue
 */

void __po_hi_gqueue_store_out (__po_hi_task_id id,
                               __po_hi_local_port_t port,
                               __po_hi_request_t* request);
/* Store a value for an OUT port.
 *
 * The id argument correspond to the task-id which own the global
 * queue. The second argument is the port that store the value. The
 * last argument is the request to store in the queue.
 */

/*
int __po_hi_gqueue_send_output (__po_hi_task_id id,
                                 __po_hi_port_t port);
*/
/*
 * Send a value for an out port.
 *
 * The first argument is the id of the task which have the global
 * queue. The second argument is the number of port that will send the
 * data
 */


int __po_hi_gqueue_get_value(__po_hi_task_id id,
			     __po_hi_local_port_t port,
			     __po_hi_request_t* request);
/*
 * Get the value on the specified port.
 *
 * The id parameter corresponds to the task-id in the local
 * process. The port argument is the number of the port that received
 * the data. The request argument is a pointer to store the received
 * data. If the port is an output, this function will return nothing,
 * but will not produce an error.
 */

int __po_hi_gqueue_next_value(__po_hi_task_id id,
			      __po_hi_local_port_t port);
/*
 * Dequeue the value on a port. The argument id is the task identifier
 * in the local process. The second argument is the port number for
 * the thread. This function should not be called several times, until
 * you know what you do.
 */

int __po_hi_gqueue_get_count(__po_hi_task_id id,
			     __po_hi_local_port_t port);
/*
 * Return the number of events that are pending of a port. The first
 * argument is the task identifier in the local process. The second
 * argument is the port identifier (or port number) for the thread.
 */

void __po_hi_gqueue_wait_for_incoming_event(__po_hi_task_id id,
					    __po_hi_local_port_t* port);
/*
 * Wait until an event is received on any port for a given thread. The
 * first argument is the thread identifier in the local process. The
 * second argument is a pointer to a port value. When the function
 * returns, the port argument will contrain the port-id that received
 * the event.
 */

__po_hi_port_id_t __po_hi_gqueue_store_in (__po_hi_task_id id,
					 __po_hi_local_port_t port,
					 __po_hi_request_t* request);
/*
 * Store a value in a IN port. The first argument is the task
 * identifier in the local process. The second argument is the port
 * identifier for the local thread. The request argument contrains the
 * request that will be stored in the queue.
 */

__po_hi_request_t*  __po_hi_gqueue_get_most_recent_value
         (const __po_hi_task_id task_id,
          const __po_hi_local_port_t local_port);


__po_hi_port_t __po_hi_gqueue_get_destination (const __po_hi_task_id task_id,
                                               const __po_hi_local_port_t local_port,
                                               const uint8_t destination_number);

uint8_t __po_hi_gqueue_get_destinations_number (const __po_hi_task_id task_id,
                                                const __po_hi_local_port_t local_port);

/*
 * Access the size of a port. The first argument is the task
 * identifier in the local process. The second argument is the port
 * identifier for the local thread.
 */

__po_hi_port_id_t __po_hi_gqueue_get_port_size(const __po_hi_task_id id,
                                            const __po_hi_local_port_t port);

/*
 * Access the used size of a port. The first argument is the task
 * identifier in the local process. The second argument is the port
 * identifier for the local thread.
 */

__po_hi_port_id_t __po_hi_gqueue_used_size( __po_hi_task_id id, __po_hi_local_port_t port);

__po_hi_port_id_t  po_hi_gqueues_queue_is_empty(__po_hi_task_id id);

__po_hi_request_t* __po_hi_gqueues_get_request(__po_hi_task_id id, __po_hi_local_port_t port);

#endif /* __PO_HI_GQUEUE_H__ */

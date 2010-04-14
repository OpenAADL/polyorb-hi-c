/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#ifndef __PO_HI_TASK_H__
#define __PO_HI_TASK_H__

#if defined(POSIX) || defined (RTEMS_POSIX)
#include <semaphore.h>
#include <po_hi_time.h>
#include <pthread.h>
#include <sched.h>
#define __PO_HI_MAX_PRIORITY sched_get_priority_max(SCHED_FIFO)
#define __PO_HI_MIN_PRIORITY sched_get_priority_min(SCHED_FIFO)
#define __PO_HI_DEFAULT_PRIORITY ((sched_get_priority_min(SCHED_FIFO) + sched_get_priority_max(SCHED_FIFO))/2)

#elif defined(RTEMS_PURE)
#include <rtems.h>
#include <inttypes.h>
#include <bsp.h>
#endif

#include <po_hi_types.h>
#include <deployment.h>

typedef __po_hi_uint16_t __po_hi_priority_t;
typedef size_t __po_hi_stack_t;

/*
 * Initialize tasking entities
 * Returns SUCCESS if there is no error.
 */
int __po_hi_initialize_tasking();

/*
 * Create a periodic task. 
 * 
 * The task created have the identifier given by the first
 * parameter. It is created according to the period created
 * with __po_hi_* functions (like __po_hi_milliseconds())
 * and priority parameters (use the OS priority). The task execute
 * periodically start_routine.
 *
 * This function returns SUCCESS if there is no error. Else, 
 * it returns the negative value ERROR_CREATE_TASK.
 */
int __po_hi_create_periodic_task (__po_hi_task_id      id, 
				  __po_hi_time_t       period, 
				  __po_hi_priority_t   priority, 
				  __po_hi_stack_t      stack_size,
				  void*                (*start_routine)(void));

/*
 * Create a sporadic task. 
 *
 * The identifier of the task is the first parameter. The period and
 * the priority of the task are stored in the second and third
 * parameter.  The code executed by the task is stored in the
 * start_routine pointer.
 * 
 * Returns SUCCESS value if there is no error. Else, returns the negative
 * value ERROR_CREATE_TASK
 */
int __po_hi_create_sporadic_task (__po_hi_task_id      id,
				  __po_hi_time_t       period, 
				  __po_hi_priority_t   priority, 
				  __po_hi_stack_t      stack_size,
				  void*                (*start_routine)(void));

/*
 * Create a generic task
 *
 * The identifier of the task is the first parameter. The period and
 * the priority of the task are stored in the second and third
 * parameter.  The code executed by the task is stored in the
 * start_routine pointer.
 * 
 * Returns SUCCESS value if there is no error. Else, returns the negative
 * value ERROR_CREATE_TASK
 */
int __po_hi_create_generic_task (__po_hi_task_id    id, 
                                 __po_hi_time_t     period, 
                                 __po_hi_priority_t priority, 
                                 __po_hi_stack_t   stack_size,
                                 void*              (*start_routine)(void));

/*
 * Wait the end of all tasks.
 * This function typically never ends, because all tasks
 * are doing an infinite loop and never ends. It just
 * used to avoid an infinite loop in the main thread.
 */
void __po_hi_wait_for_tasks ();

/*
 * Called by a periodic task, to wait for its next period
 * The argument is the task identifier
 * Returns SUCCESS value, and if fails, returns a negative value
 */
int __po_hi_wait_for_next_period (__po_hi_task_id task);

/*
 * Sleep until the time given in argument. The second
 * argument is the task identifier which will sleep.
 * Return SUCCESS if there is no error. Else, it returns
 * a negative value : ERROR_CLOCK or ERROR_PTHREAD_COND
 */
 int __po_hi_task_delay_until (__po_hi_time_t time, __po_hi_task_id task);

/*
 * Computer the next period for a task, according to the period
 * argument given at initialization time. The argument task
 * is the task-identifier in the node (__po_hi_task_id type).
 */
 int __po_hi_compute_next_period (__po_hi_task_id task);

#endif /* __PO_HI_TASK_H__ */ 

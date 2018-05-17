/******************************************************************************
 * User-mode thread library
 *
 * This library relies on <ucontext.h> to define a limited runtime to
 * support threads and various scheduling policies.
 ******************************************************************************/

#ifndef __UM_THREADS_H__
#define __UM_THREADS_H__

#include<ucontext.h>
#include<deployment.h>
#include<po_hi_task.h>
#include<po_hi_time.h>
#include<stdint.h>

#define STACKSIZE (128 * 1024)      /* Default stack size */
#define INTERVAL 700                /* timer interval in microseconds         */


/******************************************************************************/
/* Thread entities                                                            */

typedef uint32_t um_thread_id;  /* id of a thread         */
typedef uint32_t stack_size_t;  /* stack size of a thread */
typedef uint32_t priority_t;    /* priority               */

typedef enum { IDLE, READY, RUNNING } thread_state_t;

typedef struct {                /* thread control block   */
  ucontext_t     um_context;
  um_thread_id   tid;
  stack_size_t   stack_size;
  priority_t     priority;
  thread_state_t state;
} um_thread_t;

um_thread_id um_thread_create
(void (*function)(void),
 stack_size_t stack_size,
 priority_t priority);
/* um_thread_create: helper function to create a thread context
 * - initialize the context,
 * - setup the new stack,
 * - signal mask,
 * - function to execute
 */

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
int um_thread_sim_create
(void* (*function)(void),
 stack_size_t stack_size,
 priority_t priority,
 const __po_hi_task_id po_hi_id);

void um_thread_yield (void);
/* um_thread_yield: relinquish CPU */

ucontext_t *get_context (um_thread_id tid);

ucontext_t *get_current_context (void);
um_thread_id get_current_context_id (void);

/******************************************************************************/
/* Scheduler                                                                  */

typedef um_thread_id (* scheduler_function) (void);

void configure_scheduler (scheduler_function s);
void start_scheduler (void);
void scheduler(void);

/******************************************************************************/
#endif /* __UM_THREADS_H__ */

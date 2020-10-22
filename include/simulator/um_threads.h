/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2020 OpenAADL
 */

/******************************************************************************
 * User-mode thread library
 *
 * This library relies on <ucontext.h> to define a limited runtime to
 * support threads and various scheduling policies.
 ******************************************************************************/

#ifndef __UM_THREADS_H__
#define __UM_THREADS_H__

#include<ucontext.h>
#include<stdint.h>
#include<time.h>
#include<stdbool.h>

#include<po_hi_time.h>
#include<po_hi_protected.h>

#define MAX(a,b) (((a)>(b))?(a):(b))

/*****************************************************************************/
/* CONSTANTS */
#define MAX_THREADS 10              /* Maximum number of threads */
#define STACKSIZE (1024 * 1024)      /* Default stack size */
#define INTERVAL 700                /* timer interval in microseconds */

#define MAX_CORE 1

/*****************************************************************************/

typedef struct __po_hi_time_t abs_time;
//typedef struct timespec abs_time;

/* Thread entities                                                           */

typedef uint32_t um_thread_id;   /* id of a thread         */
typedef uint32_t stack_size_t;  /* stack size of a thread */
typedef uint32_t priority_t;    /* priority               */

typedef enum { WAITING, READY, RUNNING } thread_state_t;

typedef struct {                /* thread control block   */
  ucontext_t     um_context;
  um_thread_id   tid;
  stack_size_t   stack_size;
  priority_t     priority;
  thread_state_t state;
  __po_hi_time_t period;
  __po_hi_time_t next_activation; /* the reactivation time of a task is
                                     * relatif to the simulated clock        */
} um_thread_t;

extern um_thread_t threads[MAX_THREADS];
/* Array of threads currently configured in the program */
extern uint32_t um_thread_index;

extern uint32_t nb_waiting_threads;

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

um_thread_id um_thread_periodic_create
(void (*function)(void),
 stack_size_t stack_size,
 priority_t priority,
 __po_hi_time_t period);

void um_thread_yield (void);
/* um_thread_yield: relinquish CPU */

void um_wait_all (void);
/* block until all threads joined this function */

void swap_to_scheduler_context (void);

ucontext_t *get_context (um_thread_id tid);

ucontext_t *get_current_context (void);
um_thread_id get_current_context_id (void);
um_thread_id get_nb_waiting_threads (void);
__po_hi_time_t get_thread_period (um_thread_id tid);

/*****************************************************************************/
void set_next_activation (um_thread_id tid, __po_hi_time_t next_activation);

__po_hi_time_t shift(__po_hi_uint32_t second, __po_hi_uint32_t nanosecond);

__po_hi_time_t add_times (__po_hi_time_t left, __po_hi_time_t right);

/* convert_seconds_to_abs_time converts the amount of time in seconds
 * to an abs_time value.
 */
__po_hi_time_t convert_seconds_to_abs_time (uint32_t seconds);

/*****************************************************************************/
/* Scheduler                                                                 */

typedef um_thread_id (* scheduler_function) (void);

void configure_scheduler (scheduler_function s);
void start_scheduler (void);
void scheduler(void);
void control_scheduler (void);

/* FIFO within priority scheduling policy.                                   */
um_thread_id scheduler_fifo (void);

void configure_fifo_scheduler (void);
/* Configure the FIFO within priority scheduler, Only one thread by priority. */

/*****************************************************************************/

/* Waiting List                                                              */

typedef struct _waiting_list {
        __po_hi_time_t t; /* deadline of the waiting thread */
        um_thread_id tid;
        struct _waiting_list *next;
} waiting_list;

extern waiting_list *w_list;

void delay_until(um_thread_id tid, __po_hi_time_t n_time);

void delay_until_for_a_given_thread(um_thread_id tid, __po_hi_time_t n_time);

void do_awake_list(void);

/*****************************************************************************/
/* Timer utilities */

void setup_timer(uint32_t period, bool periodic);
/* activate a periodic timer of "period" ms */

void init_timer();

void stop_timer();

void set_timer_next(void);

void set_timer_after_resuming_execution(__po_hi_time_t resume_execution_time);
/*****************************************************************************/
/* Semaphore */

typedef struct _wait_list {
        um_thread_id tid;
        struct _wait_list *next;
} wait_list;

typedef struct _semaphore {
  int value;
  um_thread_id tid;
  wait_list *h_list;
  wait_list *t_list;
  int name;
} semaphore;

void semaphore_init(semaphore *s, int value, int name);
void semaphore_wait(semaphore *s);
void semaphore_post(semaphore *s);

/*****************************************************************************/
/* Mutex */

typedef struct _mutex {
        int priority;
        int previous_priority;
} mutex;

void mutex_init(__po_hi_mutex_t* m, int priority);

void mutex_lock(__po_hi_mutex_t* m);

void mutex_unlock(__po_hi_mutex_t* m);
/*****************************************************************************/
#endif /* __UM_THREADS_H__ */

/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2017 ESA & ISAE.
 */

#include<signal.h>
#include<stdlib.h>
#include<stdio.h>
#include<sys/types.h>
#include<sys/time.h>

#include<ucontext.h>
#include<stdio.h>
#include<assert.h>

#include <po_hi_debug.h>
#include <activity.h>
#include <deployment.h>
#include "subprograms.h"

#include "um_threads.h"

/******************************************************************************/
void configure_fifo_scheduler (void);

um_thread_t threads[__PO_HI_NB_TASKS]; /* XXXX */

uint32_t um_thread_index = 0;

int sched_current_context_id = 0;  /* Current thread executing                */
ucontext_t *sched_context;         /* a pointer to the running thread         */

scheduler_function the_scheduler;

/******************************************************************************/
um_thread_id um_thread_create
(void (*function)(void),
 stack_size_t stack_size,
 priority_t priority)
{
  void *stack;
  int err;
  printf ("o< \n");
  __DEBUGMSG ("[CREATE] 1\n");
  err = getcontext(&(threads[um_thread_index].um_context));
  if (err < 0)
    perror("getcontext");

  if (stack_size == 0)
    threads[um_thread_index].stack_size = STACKSIZE;
  else
    threads[um_thread_index].stack_size = stack_size;

  /* Allocate memory for the thread stack */
  stack = malloc(threads[um_thread_index].stack_size);
  if (stack == NULL) {
    perror("malloc");
    exit(1);
  }

  /* Initialze the  ucontext structure:
   * - stack and stack size
   * - reset sigmask
   */
  threads[um_thread_index].um_context.uc_stack.ss_sp    = stack;
  threads[um_thread_index].um_context.uc_stack.ss_size
    = threads[um_thread_index].stack_size;

  threads[um_thread_index].um_context.uc_stack.ss_flags = 0;
  sigemptyset(&threads[um_thread_index].um_context.uc_sigmask);

  /* Attach user function */
  makecontext(&threads[um_thread_index].um_context, function, 0);

  /* Update internal arrays of threads */
  threads[um_thread_index].tid = um_thread_index;
  threads[um_thread_index].priority = priority;
  threads[um_thread_index].state = READY;

  /*  debug_printf("Created thread context: %p, tid %d, function %p\n",
	 &(threads[um_thread_index].um_context), threads[um_thread_index].tid,
	 function);
  */
  return um_thread_index++;
}

/******************************************************************************/
ucontext_t *get_context (um_thread_id tid) {
  return &(threads[tid].um_context);
}

/******************************************************************************/
ucontext_t *get_current_context (void) {
  return sched_context;
}

/******************************************************************************/
um_thread_id get_current_context_id (void) {
  return sched_current_context_id;
}

/******************************************************************************/
void start_scheduler (void) {
  configure_fifo_scheduler();

  sched_current_context_id = 0;
  sched_context = get_context(sched_current_context_id);
  __DEBUGMSG ("[UM_THREADS] Starting scheduler\n");
  scheduler();
}

/******************************************************************************/
/* The scheduling algorithm; selects the next context to run, then starts it. */

void scheduler(void)
{
  //um_thread_id previous = sched_current_context_id;
  //assert(previous);
  threads[sched_current_context_id].state = READY;
  sched_current_context_id = the_scheduler ();

  sched_context = get_context (sched_current_context_id);
  threads[sched_current_context_id].state = RUNNING;

  setcontext(sched_context); /* go */
}

/******************************************************************************/
void um_thread_yield (void) {
  scheduler ();
}

/******************************************************************************/
void configure_scheduler (scheduler_function s) {
  the_scheduler = s;
}

/******************************************************************************/
um_thread_id scheduler_fifo (void) {
  int i;
  um_thread_id elected_thread = 0;

  for (i = 0; i < __PO_HI_NB_TASKS; i++)
    if (threads[i].state == READY
        && threads[i].priority > threads[elected_thread].priority)
      elected_thread = i;

  return elected_thread;
}

/******************************************************************************/
void configure_fifo_scheduler (void) {
  configure_scheduler(scheduler_fifo); /* initialize the scheduler            */
}

/******************************************************************************/
ucontext_t signal_context;         /* the interrupt context                   */
void *signal_stack;                /* global interrupt stack                  */

/******************************************************************************/
/* Timer interrupt handler:
 * Creates a new context to run the scheduler in, masks signals, then
 * swaps contexts saving the previously executing thread and jumping
 * to the scheduler.
 */

void timer_interrupt(int j, siginfo_t *si, void *old_context)
{
  /* Create new scheduler context */
  getcontext(&signal_context);
  signal_context.uc_stack.ss_sp    = signal_stack;
  signal_context.uc_stack.ss_size  = STACKSIZE;
  signal_context.uc_stack.ss_flags = 0;
  sigemptyset(&signal_context.uc_sigmask);
  makecontext(&signal_context, scheduler, 0);

  /* Save running thread, jump to scheduler */
  swapcontext(get_current_context(), &signal_context);
}

/******************************************************************************/
/* Set up SIGALRM signal handler:
 * We use the SIGALRM signal to emulate a timer-based interrupt for
 * quantum-based scheduling policies.
 */

void setup_timer(uint32_t period, bool periodic)
{
  struct sigaction act;
  struct itimerval it;

  signal_stack = malloc(STACKSIZE); /* allocate the signal/interrupt stack    */
  if (signal_stack == NULL) {
    perror("malloc");
    exit(1);
  }

  act.sa_sigaction = timer_interrupt; /* bind function to the timer           */

  sigemptyset(&act.sa_mask); /* reset set of signals                          */
  act.sa_flags = SA_RESTART  /* interruptible functions do not raise [EINTR]  */
    | SA_SIGINFO;            /* to select particular signature signal handler */

  if(sigaction(SIGALRM, &act, NULL) != 0)
    perror("Signal handler");

  /* setup our timer */
  it.it_value.tv_sec = 0;
  it.it_value.tv_usec = period * 1000;

  if (periodic == true)
    it.it_interval = it.it_value;
  else {
    it.it_interval.tv_sec = 0;
    it.it_interval.tv_usec = 0;
  }

  if (setitimer(ITIMER_REAL, &it, NULL))
    perror("setitiimer");
}

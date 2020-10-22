/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2020 OpenAADL
 */

#include<assert.h>
#include<signal.h>
#include<stdlib.h>
#include<sys/types.h>
#include<sys/time.h>
#include<unistd.h>
#include <string.h>
#include <stdio.h>
#include <math.h>

#include "um_threads.h"

//#define __PO_HI_DEBUG_LEVEL 12

#include <po_hi_task.h>
#include <po_hi_debug.h>

void print_timestamp (void);
/* Print a timestamp */

/******************************************************************************/
/* PRINT DEBUG*/
void print_timestamp (void) {
  __po_hi_time_t tp;
  __po_hi_get_time(&tp);

  __PO_HI_DEBUG_INFO ("[%d.%d] ", (int) tp.sec % 1000, tp.nsec/CLOCKS_PER_SEC);
}

/******************************************************************************/
/* Simulated Clock is used to enable the user to suspend the execution
 * and then resume it without altering behavior of threads and
 * scheduler */

um_thread_t threads[MAX_THREADS];

uint32_t um_thread_index = 0;

uint32_t nb_waiting_threads = 0;

int sched_current_context_id = 0;  /* Current thread executing                */
ucontext_t *sched_context;         /* a pointer to the running thread         */
um_thread_id sched_previous_thread_id;

/*The "main" execution context */
ucontext_t maincontext; // XXXX

scheduler_function the_scheduler;

/* w_list is a list of waiting threads sorted by their
 * time of waiting that is specified by : w_list->t */
waiting_list *w_list = NULL;

ucontext_t yield_context;
void* yield_stack;

void *signal_stack;               /* global interrupt stack                   */
struct sigaction alarm_sigact;

bool control_scheduler_dispatch_when_idle = true;
bool first_execution_of_control_scheduler = true;
um_thread_id control_scheduler_id;
um_thread_id idle_job_id;

void idle_job (void);

/******************************************************************************/
um_thread_id um_thread_create
(void (*function)(void),
 stack_size_t stack_size,
 priority_t priority)
{
  void *stack;
  int err;

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
  threads[um_thread_index].um_context.uc_link = &maincontext;
  threads[um_thread_index].um_context.uc_stack.ss_sp = stack;
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

  __PO_HI_DEBUG_INFO("Created thread context: %p, tid %d, priority %d, function %p\n",
         &(threads[um_thread_index].um_context), threads[um_thread_index].tid,
               priority, function);

  return um_thread_index++;
}

/******************************************************************************/
um_thread_id um_thread_periodic_create
(void (*function)(void),
 stack_size_t stack_size,
 priority_t priority,
 __po_hi_time_t period)
{
  um_thread_id tid = um_thread_create(function, stack_size, priority);
  threads[tid].period = period;
  return tid;
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
__po_hi_time_t get_thread_period (um_thread_id tid)
{
  return threads[tid].period;
}
/******************************************************************************/
um_thread_id get_nb_waiting_threads (void) {
  return nb_waiting_threads;
}

/******************************************************************************/
void set_next_activation (um_thread_id tid, __po_hi_time_t next_activation) {
  threads[tid].next_activation = next_activation;
}

/******************************************************************************/
/* The scheduling main loop: selects the next context to run, then starts it  */

void scheduler(void) {
  sched_previous_thread_id = sched_current_context_id;

  if ((sched_current_context_id != -1)
      && (threads[sched_current_context_id].state == RUNNING))
    {
      threads[sched_current_context_id].state = READY;
      do_awake_list();
    }

  sched_current_context_id = the_scheduler ();
  //  printf("%d %d\n", sched_current_context_id, __LINE__);
  if (sched_current_context_id == -1)
  {
    if (control_scheduler_dispatch_when_idle)
    {
      while (get_nb_waiting_threads() == um_thread_index - 1)
         do_awake_list();
      threads[control_scheduler_id].state = READY;
    }
    else
      {
        /* (get_nb_waiting_threads() == um_thread_index) ==>> control_scheduler
         * is inserted into w_list as the absolute date for its next dispatch
         * given by the user is consistent i.e. it is greater than the
         * resume_execution_time
         *
         * (get_nb_waiting_threads() == um_thread_index - 1) ==>> control_scheduler
         * is NOT inserted into w_list as the absolute date for its next dispatch
         * given by the user is NOT consistent i.e. it is smaller than
         * the resume_execution_time
         * */
        if (get_nb_waiting_threads() == um_thread_index)
          while (get_nb_waiting_threads() == um_thread_index) {
            do_awake_list();
          }
        else
          if (get_nb_waiting_threads() == (um_thread_index - 1))
            while (get_nb_waiting_threads() == (um_thread_index - 1))
             do_awake_list();

        //        printf("%d %d\n", sched_current_context_id, __LINE__);
      }
    } else {
      sched_context = get_context (sched_current_context_id);

      threads[sched_current_context_id].state = RUNNING;

      print_timestamp();
      __PO_HI_DEBUG_INFO("Swithching from %d to %d\n",
                   sched_previous_thread_id, sched_current_context_id);

      setcontext(sched_context);
    }
}

/******************************************************************************/
void start_scheduler (void) {
  sched_current_context_id = control_scheduler_id;
  sched_context = get_context(sched_current_context_id);
  __PO_HI_DEBUG_INFO("Starting scheduler @ %p\n", sched_context);
  /* Call the scheduler */
  scheduler();
}

/******************************************************************************/
void configure_scheduler (scheduler_function s) {
  um_thread_id tid;

  /* Allocate memory for the um_yield() context switch */
  yield_stack = malloc(STACKSIZE);

  /* Register idle task */
  tid = um_thread_create(idle_job, STACKSIZE, __PO_HI_MIN_PRIORITY);
  __PO_HI_DEBUG_INFO("IDLE task is created, tid = %d \n", tid);
  idle_job_id = tid;

  /* Register control_scheduler() task */
  tid = um_thread_create(control_scheduler, STACKSIZE, __PO_HI_MAX_PRIORITY);
  __PO_HI_DEBUG_INFO("control_scheduler is created, tid = %d \n", tid);
  __PO_HI_DEBUG_INFO("control_scheduler um_thread_index-1 = %d \n",
               um_thread_index-1);
  control_scheduler_id = tid;
  sched_current_context_id = tid;

  /* Register scheduler */
  the_scheduler = s;
}

/******************************************************************************/
/* The FIFO with priority scheduler */

um_thread_id scheduler_fifo (void) {

  int i;
  um_thread_id elected_thread = 0;

  /* PS: um_thread_index is the number of all the created threads */

  //  for (um_thread_id i = 0; i < um_thread_index; i++)
  //    printf("%d %d %d\n", i, threads[i].state, threads[i].priority);

  while (elected_thread < um_thread_index
         && threads[elected_thread].state != READY)
    elected_thread++;

  if (elected_thread == um_thread_index)
      elected_thread = -1;
  else
    for (i = elected_thread + 1 ; i < um_thread_index ; ++i)
      if (threads[i].state == READY
          && threads[i].priority > threads[elected_thread].priority)
        elected_thread = i;

  //  printf("FIFO: %d %d\n", elected_thread, __LINE__);
  return elected_thread;
}

void configure_fifo_scheduler (void) {
  configure_scheduler(scheduler_fifo); /* initialize the scheduler            */
  init_timer();       /* initialize the timer                                 */
}

/******************************************************************************/
/* do_awake_list this function browses the "w_list" that is a sorted
 * list of threads waiting activation. If the deadline (or period) of
 * a given thread in w_list is expired then its state is update to READY
 * and it is removed from the w_list. */

void do_awake_list(void) {
  __po_hi_time_t c_time;
  waiting_list *aux;

  if (w_list != NULL) {
    __po_hi_get_time(&c_time);
    stop_timer();
    /* awake all threads which needed and take them out of the waiting_list
     * Rq : the timer resolution is 1ms so we check within this resolution
     */
    while(w_list != NULL &&
          ((w_list->t).sec < c_time.sec ||
           ((w_list->t).sec == c_time.sec
            && ((w_list->t).nsec <= c_time.nsec + 999999L)))
          )
      {
        __PO_HI_DEBUG_INFO("----> %d (%d.%d)\n",
                     w_list->tid,
                     (int)(w_list->t).sec % 1000,
                     (long)(w_list->t).nsec/CLOCKS_PER_SEC);

        threads[w_list->tid].state = READY;
        nb_waiting_threads--;
        aux = w_list->next;
        free(w_list);
        w_list = aux;
      }

    /* set the time for the next thread */
    set_timer_next();
  }

  return;
}

/******************************************************************************/
void swap_to_scheduler_context (void) {
  ucontext_t yield_context;
  /* Create new scheduler context */
  getcontext(&yield_context);
  yield_context.uc_link = &maincontext;
  yield_context.uc_stack.ss_sp    = yield_stack;
  yield_context.uc_stack.ss_size  = STACKSIZE;
  yield_context.uc_stack.ss_flags = 0;
  sigemptyset(&yield_context.uc_sigmask);
  makecontext(&yield_context, scheduler, 0);

  /* Save running thread, jump to scheduler */
  swapcontext(get_current_context(), &yield_context);
}

/******************************************************************************/
void um_wait_all (void) {
  static int blocked_tasks = 0;

  if (sched_context == NULL)
    return;

  blocked_tasks++;

  if (blocked_tasks == um_thread_index - 2) {
    for (um_thread_id i = 0; i < um_thread_index- 2; i++) {
      threads[i].state = READY;
    }
    swap_to_scheduler_context();

  } else {
    um_thread_yield();
  }
}

/******************************************************************************/
void um_thread_yield (void) {

  /* The current task is now waiting */
  threads[get_current_context_id()].state = WAITING;

  swap_to_scheduler_context();
}

/******************************************************************************/
/* SIGUSR1 handler: whenever the process receives SIGUSR1, we force
   the scheduler to call the control_scheduler function
 */

void SIGUSR1_sigaction(int signo, siginfo_t *info, void *context)
{
  threads[0].state = READY; // XXX
}

/******************************************************************************/
/* Setup SIGUSR signal handler */

void setup_SIGUSR1_handler(void)
{
  struct sigaction act;

  /* allocate the signal/interrupt stack   */

  act.sa_sigaction = SIGUSR1_sigaction;

  sigemptyset(&act.sa_mask); /* reset set of signals                          */
  act.sa_flags = SA_RESTART /* interruptible functions do not raise [EINTR]   */
    | SA_SIGINFO;           /* to select particular signature signal handler  */

  if(sigaction(SIGUSR1, &act, NULL) != 0)
    perror("Error: cannot handle SIGUSR1"); /* should not happen */

}

/******************************************************************************/
__po_hi_time_t shift(__po_hi_uint32_t second, __po_hi_uint32_t nanosecond) {
  __po_hi_time_t c_time;
  __po_hi_get_time(&c_time);

  __po_hi_uint32_t aux = c_time.nsec + nanosecond;

  c_time.sec += second + aux/1000000000L;
  c_time.nsec = aux % 1000000000L;

  return c_time;
}

/******************************************************************************/
__po_hi_time_t add_times (__po_hi_time_t left, __po_hi_time_t right)
{
   __po_hi_time_t result;
   result.sec    = left.sec + right.sec;
   result.nsec   = left.nsec + right.nsec;
   while (result.nsec > 1000000000)
   {
      result.sec = result.sec + 1;
      result.nsec = result.nsec - 1000000000;
   }
   return result;
}

/******************************************************************************/
__po_hi_time_t subtract_times (__po_hi_time_t left, __po_hi_time_t right)
{
   __po_hi_time_t result;
   result.sec    = left.sec - right.sec;

   if (left.nsec < right.nsec)
   {
           result.sec = result.sec - 1;
           result.nsec = 1000000000 - (right.nsec - left.nsec);
   }
   else
   {
           result.nsec = left.nsec - right.nsec;
       while (result.nsec > 1000000000)
       {
          result.sec = result.sec + 1;
          result.nsec = result.nsec - 1000000000;
       }
    }

   return result;
}

/******************************************************************************/
__po_hi_time_t convert_seconds_to_abs_time (uint32_t seconds)
{
   __po_hi_time_t result;
   result.sec    = seconds;
   result.nsec   = 0;
   return result;
}
/******************************************************************************/
void idle_job (void) {

  while (1) {}

}

/******************************************************************************/
void control_scheduler (void) {

  while (1) {
  __po_hi_time_t c_time, suspend_execution_time, resume_execution_time,
    suspension_duration;
  int suspension_d;

  /* First, we stop the simulated clock */
  stop_timer();

  __po_hi_get_time(&suspend_execution_time);

  printf ("control_scheduler :: suspend_execution_time = %d.%d \n",
          (int) suspend_execution_time.sec % 1000,
          suspend_execution_time.nsec / CLOCKS_PER_SEC);

  /* First, we ask the user for the duration of the suspension */
  printf("\n Enter the duration of the execution suspension (in sec) : ");
  fflush(stdout);
  scanf("%d", &suspension_d);

  suspension_duration.sec = suspension_d;
  suspension_duration.nsec = 0;

  __po_hi_get_time(&c_time);
  __PO_HI_DEBUG_INFO ("control_scheduler :: current_time = %d.%d \n",
                (int) c_time.sec % 1000,
                c_time.nsec / CLOCKS_PER_SEC);

  /* We must activate a timer to resume the execution after the
   * specified suspension duration. Before the activation of the
   * timer, we must compute the next activation of all threads */

  resume_execution_time = add_times(c_time, suspension_duration);
  __PO_HI_DEBUG_INFO ("control_scheduler :: resume_execution_time = %d.%d \n",
                (int) resume_execution_time.sec % 1000,
                resume_execution_time.nsec/CLOCKS_PER_SEC);

  /* Then, we ask the user to choose the next manner of dispatch of
   * the control_scheduler task among the two following proposals:
   *
   * 1) control_sechdule is dispatched when the scheduler is idle, in
   * this case we change its priority to the lowest priority.
   *
   * 2) control_sechdule is dispatched in a later date chosen by the
   * user, in this case we save its priority which is the highest one
   * and we call delay_until the given date. */

  char dispatch_choice[20];
  printf("\n Please choose the next moment to dispatch control_scheduler task : \n"
  "- 'i' dispatch when the scheduler is idle. \n"
  "- 'd-<absolute date in sec>' to choose a dispatch in an absolute date : "
  "i.e. the dispatch will be in the first time the scheduler is idle "
  "after this date. \n dispatch_choice : ");
  fflush(stdout);
  scanf("%s", dispatch_choice);
  const char s[2] = "-";
  char *c;

  fflush(stdout);
  /* get the first token */
  c = strtok(dispatch_choice, s);

  fflush(stdout);

  if (strcmp(c,"i") == 0) {
    __PO_HI_DEBUG_INFO("Dispatch choice is idle. \n");
    control_scheduler_dispatch_when_idle = true;

    /* We assign the control_scheduler task with the lowset priority */
    threads[control_scheduler_id].priority = 1;

  } else if (strcmp(c,"d") == 0) {
    control_scheduler_dispatch_when_idle = false;
    c = strtok(NULL, s);
    __PO_HI_DEBUG_INFO("Dispatch choice is a next absolute date (in sec): %d. \n",
                 atoi(c));
  }

  __PO_HI_DEBUG_INFO ("%d\n",__LINE__);
  /* The update of the next activation of threads is only made
   * when the suspension is triggered by a SIGUSR1 signal */
  if (!first_execution_of_control_scheduler)
  {
    __po_hi_time_t offset;
    for(um_thread_id i = 0; i < um_thread_index-2; i++)
    {
      __PO_HI_DEBUG_INFO ("%d\n",__LINE__);
      offset = subtract_times (threads[i].next_activation,
                               suspend_execution_time);
      threads[i].next_activation = add_times(resume_execution_time, offset);
      __PO_HI_DEBUG_INFO ("threads[%d].next_activation = %d.%d \n", i,
       (int) threads[i].next_activation.sec % 1000,
       threads[i].next_activation.nsec/CLOCKS_PER_SEC);
    }

    /* we must update deadlines of waiting threads in w_list
     * according to their next_activation */
    waiting_list *aux;
    aux = w_list;
    while (aux != NULL)
    {
      aux->t = threads[aux->tid].next_activation;
      aux = aux->next;
    }

    __po_hi_get_time(&c_time);
    __PO_HI_DEBUG_INFO ("control_scheduler :: current_time = %d.%d \n",
                  (int) c_time.sec % 1000, c_time.nsec/CLOCKS_PER_SEC);

    /* in the case when user opts for the absolute date dispatch choice */
    if (!control_scheduler_dispatch_when_idle) {
      __PO_HI_DEBUG_INFO ("%d %c\n",__LINE__,c);
      threads[control_scheduler_id].next_activation.sec
        = atoi(c) + floor(c_time.sec/1000) * 1000;
      threads[control_scheduler_id].next_activation.nsec = 0;
      __PO_HI_DEBUG_INFO ("threads[%d].next_activation = %d.%d \n",
        control_scheduler_id,
        (int) threads[control_scheduler_id].next_activation.sec % 1000,
        threads[control_scheduler_id].next_activation.nsec/CLOCKS_PER_SEC);
      delay_until_for_a_given_thread
        (control_scheduler_id,
         threads[control_scheduler_id].next_activation);
    }
    __PO_HI_DEBUG_INFO ("coucou\n");
    set_timer_after_resuming_execution(resume_execution_time);
    //    um_thread_yield ();
  } else {
  /* the case when first_execution_of_control_scheduler == true
   * i.e. at the beggining of the simulation as the
   * control_scheduler task is the first task to be executed
   */
      __PO_HI_DEBUG_INFO ("%d\n",__LINE__);
      first_execution_of_control_scheduler = false;
      threads[control_scheduler_id].state = WAITING;

      /* set timer for the resume_execution */
      __po_hi_get_time(&c_time);
      __PO_HI_DEBUG_INFO ("*** control_scheduler :: current_time = %d.%d ***\n",
                    (int) c_time.sec % 1000, c_time.nsec/CLOCKS_PER_SEC);

      for (um_thread_id i=0; i < control_scheduler_id; i++) {
        __PO_HI_DEBUG_INFO ("%d %d\n", i, __LINE__);
        delay_until_for_a_given_thread(i, resume_execution_time);
      }

      /* in the case when user opts for the absolute date dispatch choice */
      if (!control_scheduler_dispatch_when_idle) {
        threads[control_scheduler_id].next_activation.sec =
          atoi(c) + (floor(c_time.sec/1000) + 1) * 1000;
        threads[control_scheduler_id].next_activation.nsec = 0;
        __PO_HI_DEBUG_INFO
          ("threads[%d].next_activation = %d.%d \n",
           control_scheduler_id,
           (int) threads[control_scheduler_id].next_activation.sec % 1000,
           threads[control_scheduler_id].next_activation.nsec/CLOCKS_PER_SEC);
        delay_until_for_a_given_thread
          (control_scheduler_id, threads[control_scheduler_id].next_activation);

        __PO_HI_DEBUG_INFO ("%d\n",__LINE__);
        set_timer_next();
        __PO_HI_DEBUG_INFO ("%d\n",__LINE__);
        um_thread_yield ();
        __PO_HI_DEBUG_INFO ("%d\n",__LINE__);
      } else {
        set_timer_next();
        swap_to_scheduler_context(); // We do not want to go in the waiting state
      }
  }
}

void print_node (waiting_list *n) {
  if (n != NULL)
    __PO_HI_DEBUG_INFO ("%d (%d.%ld) ->",  n->tid, (n->t).sec, (n->t).nsec);
}

void print_waiting_list (waiting_list *l) {
 waiting_list *aux;
 aux = l;
 __PO_HI_DEBUG_INFO ("w_list:");
 while (aux != NULL) {
   print_node (aux);
   aux = aux-> next;
 }
 __PO_HI_DEBUG_INFO ("\n");
}

/******************************************************************************/
void insert_into_waiting_list(um_thread_id tid, __po_hi_time_t n_time) {

  stop_timer();
  waiting_list *insert, *prec, *aux;
  /* set the thread to WAITING */
  if (tid == idle_job_id) {
    return;
  }

  /*  printf("Task %d goes to WAITING until %d %ld\n",
         tid, n_time.sec, n_time.nsec);
  */
  threads[tid].state = WAITING;
  nb_waiting_threads++;

  //  print_waiting_list (w_list);

  /* Insertion of the thread in the sorted waiting list */
  aux = malloc(sizeof(waiting_list));
  aux->t = n_time;
  aux->tid = tid;
  aux->next=NULL;

  /* head insertion */
  if (w_list == NULL
      || (w_list->t).sec > n_time.sec
      || (((w_list->t).sec == n_time.sec
           && ((w_list->t).nsec > n_time.nsec)))) {
    aux->next = w_list;
    w_list = aux;

  } else {
    prec = w_list;
    insert = w_list;
    while (insert != NULL && ((insert->t).sec < n_time.sec ||
                              ((insert->t).sec == n_time.sec &&
                               (insert->t).nsec <= n_time.nsec))) {
      prec = insert;
      insert = insert->next;
    }
    prec->next = aux;
    if (insert != w_list)
      aux->next = insert;
  }
  print_waiting_list (w_list);
}

/******************************************************************************/
void delay_until(um_thread_id tid, __po_hi_time_t n_time) {

  __po_hi_time_t c_time;
  __po_hi_get_time(&c_time);

  /* Check if the n_time is positive and at least 1ms */
  if (n_time.sec < c_time.sec
      || (n_time.sec == c_time.sec
          && n_time.nsec < c_time.nsec + 1000000L))
    return;

  insert_into_waiting_list (tid, n_time);

  set_timer_next();

  /* yield the thread */
  um_thread_yield ();
}

/******************************************************************************/
void delay_until_for_a_given_thread(um_thread_id tid, __po_hi_time_t n_time) {

  __po_hi_time_t c_time;
  __po_hi_get_time(&c_time);

  /* Check if the n_time is positive and at least 1ms */
  assert (n_time.sec > c_time.sec ||
          (n_time.sec == c_time.sec && n_time.nsec >= c_time.nsec));
  //    return;

  insert_into_waiting_list (tid, n_time);
}

/******************************************************************************/
/* Timer interrupt handler:
 * Creates a new context to run the scheduler in, masks signals, then
 * swaps contexts saving the previously executing thread and jumping
 * to the scheduler.
 */

void timer_interrupt(int j, siginfo_t *si, void *old_context)
{
  /* the interrupt context */
  ucontext_t signal_context;
  /* Create new scheduler context */
  getcontext(&signal_context);
  signal_context.uc_stack.ss_sp    = signal_stack;
  signal_context.uc_stack.ss_size  = STACKSIZE;
  signal_context.uc_stack.ss_flags = 0;
  signal_context.uc_link = NULL;
  sigemptyset(&signal_context.uc_sigmask);
  makecontext(&signal_context, scheduler, 0);

  /* Save running thread, jump to scheduler */
  swapcontext(get_current_context(), &signal_context);
}

void init_timer(void) {

  signal_stack = malloc(STACKSIZE); /* allocate the signal/interrupt stack   */
  if (signal_stack == NULL) {
    perror("malloc");
    exit(1);
  }

  alarm_sigact.sa_sigaction = timer_interrupt; /* bind function to the timer           */
}

/* Set up SIGALRM signal handler:
 * We use the SIGALRM signal to emulate a timer-based interrupt for
 * quantum-based scheduling policies.
 */

void setup_timer(uint32_t period, bool periodic)
{
  struct itimerval it;

  sigemptyset(&alarm_sigact.sa_mask); /* reset set of signals                 */
  alarm_sigact.sa_flags = SA_RESTART  /* interruptible functions do not raise [EINTR]  */
    | SA_SIGINFO;            /* to select particular signature signal handler */

  if(sigaction(SIGALRM, &alarm_sigact, NULL) != 0)
    perror("Signal handler");

  /* setup our timer */
  it.it_value.tv_sec = period/1000;
  it.it_value.tv_usec = (period % 1000) * 1000;

  if (periodic)
    it.it_interval = it.it_value;
  else {
    it.it_interval.tv_sec = 0;
    it.it_interval.tv_usec = 0;
  }

  if (setitimer(ITIMER_REAL, &it, NULL))
    perror("setitiimer");
}

void stop_timer() {
        if (setitimer(ITIMER_REAL, NULL, NULL))
    perror("setitiimer");
}

void set_timer_next() {
  __po_hi_time_t c_time;

  if (w_list != NULL) {
    __po_hi_get_time(&c_time);
    __PO_HI_DEBUG_INFO("Next_timer ----> %d (%d.%d)\n",
                       w_list->tid, (int)(w_list->t).sec,
                       (long)(w_list->t).nsec/CLOCKS_PER_SEC);

    setup_timer((int) (((w_list->t).sec - c_time.sec) * 1000
                       + ((w_list->t).nsec - c_time.nsec)/1000000), false);
  }
}

void set_timer_after_resuming_execution(__po_hi_time_t resume_execution_time) {
  __po_hi_time_t c_time;

  if (w_list != NULL)
  {
    c_time = resume_execution_time;
    setup_timer((int) (((w_list->t).sec - c_time.sec) * 1000
              + ((w_list->t).nsec - c_time.nsec)/1000000),
                false);
  }
}
/******************************************************************************/
/* Semaphore */

void semaphore_init(semaphore *s, int value_, int name_) {
  s->value = value_;
  s->h_list = malloc(sizeof(wait_list));
  s->t_list = s->h_list;
  (s->t_list)->tid = MAX_THREADS;
  (s->t_list)->next = NULL;
  (s->name) = name_;
}

/******************************************************************************/
void semaphore_wait(semaphore *s) {

  if (s->tid == get_current_context()) {
    __PO_HI_DEBUG_INFO ("&&&&&&&& task %d already has the semaphore, exiting\n", s->tid);
    return;
  }

  stop_timer();

  if (s->value == 0) { // or while?
    (s->t_list)->tid = get_current_context_id();
    threads[(s->t_list)->tid].state = WAITING;
    nb_waiting_threads++;
    __PO_HI_DEBUG_INFO("<--- task %d waits for semaphore %d\n", (s->t_list)->tid, s->name);
    (s->t_list)->next = malloc(sizeof(wait_list));
    s->t_list = (s->t_list)->next;
    (s->t_list)->tid = MAX_THREADS;
    (s->t_list)->next = NULL;

    set_timer_next();
    swap_to_scheduler_context();
  };

  s->value--;
  s->tid = get_current_context_id();
  assert (s->value >= 0);
  __PO_HI_DEBUG_INFO("<--- %d task %d gets semaphore %d %d\n", __LINE__,
               get_current_context_id(), s->name,s->value);

  set_timer_next();
}


void semaphore_post(semaphore *s) {
  wait_list *aux;

  stop_timer();
  __PO_HI_DEBUG_INFO("**** %d posting semaphore %d\n",
               get_current_context_id(),
               s->name);

  if (((s->h_list)->tid) < MAX_THREADS) {
    threads[(s->h_list)->tid].state = READY;
    nb_waiting_threads--;
    __PO_HI_DEBUG_INFO("---> task %d released by semaphore %d\n", (s->h_list)->tid, s->name);
    aux = (s->h_list)->next;
    free(s->h_list);
    s->h_list = aux;
    s->value++;
    set_timer_next();
    swap_to_scheduler_context();
  } else {
    s->value++;
    set_timer_next();
  }
}
/******************************************************************************/
/* Mutex */

void mutex_init(__po_hi_mutex_t *m, int priority_) {
  m->priority = priority_;
}

void mutex_lock(__po_hi_mutex_t *m) {
  /* Deactivate the timer */
  stop_timer();

  m->previous_priority = threads[get_current_context_id()].priority;
  threads[get_current_context_id()].priority = m->priority;

  /* Reactivate the timer */
  set_timer_next();
}

void mutex_unlock(__po_hi_mutex_t *m) {
  /* Disactivate the timer */
  stop_timer();

  threads[get_current_context_id()].priority = m->previous_priority;

  swap_to_scheduler_context();
}

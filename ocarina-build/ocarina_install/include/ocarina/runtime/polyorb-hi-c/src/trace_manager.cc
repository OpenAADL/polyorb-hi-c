extern "C" {
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <request.h>
#include <pthread.h>
#include <deployment.h>
#include <po_hi_task.h>
#include <po_hi_gqueue.h>
#include <string.h>
#include <po_hi_debug.h>
}
#include <trace_manager.hh>
#include <remote_configuration.hh>
#include <activity.h>
#include <request.h>
#include <thread>
#include <mutex>
#include <state.hh>

#include <hyperperiod_config.hh>
#define TRACESIZE 1

int cpt_obs = 0;

static int hyperperiodstep = 0;
static int hyperperiodocc = -1;
static bool destroyed = false;
static pthread_mutex_t lock;
static int nb_ports_per_thread[__PO_HI_NB_TASKS];
static int thread_monitoring_table[__PO_HI_NB_TASKS];
static __po_hi_request_t static_initial_state[__PO_HI_NB_PORTS];
static std::mutex g_i_mutex, f_i_mutex, mutex, k_a_mutex;
static __po_hi_uint8_t* global_n_dest[__PO_HI_NB_TASKS];



static bool init = false;
static auto global_trace = new trace_type();//std::make_shared<trace_type>();

/*------------------------------------------------------------------------------------------------*/
// Variable declarations for update dispatch
/*------------------------------------------------------------------------------------------------*/

__po_hi_request_t* monitored_port_value;
state_type* modified_copy;

/*------------------------------------------------------------------------------------------------*/
// Tasks monitoring global variables
/*------------------------------------------------------------------------------------------------*/

static int tasks_type[__PO_HI_NB_TASKS];

void
generic_task_creation(const __po_hi_task_id      id)
{
#ifdef MONITORING
tasks_type[id]=__TRACE_GENERIC_TASK_MONITORED;
#endif
}

void
periodic_task_creation(const __po_hi_task_id      id)
{
#ifdef MONITORING
__DEBUGMSG ("periodic_task_creation\n");
tasks_type[id]=__TRACE_PERIODIC_TASK_MONITORED;
#endif
}

void
sporadic_task_creation(const __po_hi_task_id      id)
{
#ifdef MONITORING
__DEBUGMSG ("sporadic_task_creation\n");
tasks_type[id]=__TRACE_SPORADIC_TASK_MONITORED;
#endif
}

/*------------------------------------------------------------------------------------------------*/
// Trace manipulation
/*------------------------------------------------------------------------------------------------*/


auto//trace_type*
new_trace(step_type step, hyperperiod_type hyperperiod, __po_hi_request_t* initial_state)
{
  std::lock_guard<std::mutex> lock(mutex);

  if (not init){
  state_type s0;
  s0.step() = step;
  s0.hyperperiod() = hyperperiod;

  for (auto thread_id = 0ul; thread_id < ports_type::nb_threads; ++thread_id)
  {
    for (auto port_id = 0ul; port_id < ports_type::ports_for_thread[thread_id]; ++port_id)
    {
      s0.port_value(thread_id, port_id) = *initial_state;
      ++initial_state;
    }
  }
//  global_trace = std::make_shared<trace_type>();
  global_trace->push(std::move(s0));
  init = true;
  }
  return global_trace;
}

/*------------------------------------------------------------------------------------------------*/

void
set_state_port_value(__po_hi_task_id id_th, __po_hi_local_port_t port_id,__po_hi_request_t* ptr, state_type* local_state)
{
//  __po_hi_request_t* _port_value;
  //ptr = __po_hi_gqueue_get_most_recent_value (id_th,port_id);
//  __DEBUGMSG ("Before memcpy\n");
// __DEBUGMSG ("Set state port before memcopy. IF Th: %d, Pt: %d\n",id_th,port_id);
 // memcpy (_port_value, ptr, sizeof (__po_hi_request_t*));
//  __DEBUGMSG ("After memcpy\n");
// __DEBUGMSG ("Set state port after memcopy. IF Th: %d, Pt: %d, port_value: %d\n",id_th,port_id, ptr->vars);
  local_state->port_value(id_th,port_id) = *ptr;
 //__DEBUGMSG ("Set state port after port value affection. IF Th: %d, Pt: %d\n",id_th,port_id);
//  __DEBUGMSG ("After ptr affectation\n");
}

/*------------------------------------------------------------------------------------------------*/

void
init_monitored_ports_for_thread(__po_hi_task_id id_th, __po_hi_uint8_t* __po_hi_n_dest, int nb_ports)
{
#ifdef MONITORING
global_n_dest[id_th] = __po_hi_n_dest;
nb_ports_per_thread[(int)id_th] = nb_ports;
#endif
}

/*------------------------------------------------------------------------------------------------*/

int
nb_ports_for_thread(__po_hi_task_id id_th)
{
return nb_ports_per_thread[(int)id_th];
}

/*------------------------------------------------------------------------------------------------*/

void
update_periodic_dispatch (__po_hi_task_id id_th)
{
#ifdef MONITORING
//__DEBUGMSG ("******************DISPATCH OF THREAD %d*******************\n",id_th);

//std::lock_guard<std::mutex> lock(f_i_mutex);


 if (!destroyed && (tasks_type[id_th] == __TRACE_PERIODIC_TASK_MONITORED))
  {
  std::lock_guard<std::mutex> lock(f_i_mutex);
  modified_copy = new state_type{global_trace->back()};
//  auto local_state = std::make_shared<trace_type>();
  int port_id;
  for (port_id = 0 ; port_id <nb_ports_per_thread[id_th] ; port_id++){

  /*
  * If the port is an data port, we create a new state_type
  * with current value for each in data port
  */
 //__DEBUGMSG ("Quick look to the if: th-%d port-%d p-size-%d \n",id_th, port_id,__po_hi_gqueue_get_port_size(    (__po_hi_task_id)id_th,(__po_hi_local_port_t)port_id));
 __DEBUGMSG ("Update_dispatch. full_print Th: %d Po: %d Size : %d n_dest : %d empty : %d\n",id_th,port_id, __po_hi_gqueue_get_port_size(    (__po_hi_task_id)id_th,(__po_hi_local_port_t)port_id), global_n_dest[id_th][port_id], po_hi_gqueues_queue_is_empty(id_th));
  if (
  //(__po_hi_gqueue_get_port_size((__po_hi_task_id)id_th,(__po_hi_local_port_t)port_id) ==    (__po_hi_int8_t)-1
  // __PO_HI_GQUEUE_FIFO_INDATA
  //) &&
    (global_n_dest[id_th][port_id] == (__po_hi_int8_t)0)
    //&&
    //(po_hi_gqueues_queue_is_empty(id_th)==(__po_hi_int8_t)0)
    )
    {
    __DEBUGMSG ("Update_dispatch. relevant case 1111 Th: %d Po: %d \n\n\n\n",id_th,port_id);
    monitored_port_value = __po_hi_gqueue_get_most_recent_value (id_th,(__po_hi_local_port_t)port_id);

    if ((monitored_port_value->port != -1) && (monitored_port_value->port != -2))
    {__DEBUGMSG ("Update_dispatch. relevant case 2222 Th: %d Po: %d \n",id_th,port_id);}

    set_state_port_value(id_th, (__po_hi_local_port_t)port_id, monitored_port_value, modified_copy);
    }
   }
   hyperperiodstep++;
   modified_copy->step()=hyperperiodstep;
   modified_copy->thread_event()=id_th;
//   modified_copy->port_event()=;
   //display_trace_temp(global_trace);
display_state_temp(modified_copy);
  global_trace->push(std::move(*modified_copy));
  //__DEBUGMSG ("Update_dispatch. New job Th: %d Po: %d trace size: %d\n",id_th,port_id, global_trace->stack_size());
#ifdef TRACESIZE
  if ( global_trace->stack_size()%100 == 0)
  { //display_trace_temp(global_trace);
  int test = global_trace->back().my_size();
  __DEBUGMSG ("TRACE Total size-> stack length : %d, request_size : %d, test : %d total : %d\n", global_trace->stack_size(), sizeof(__po_hi_request_t),test,((global_trace->stack_size())*test));
  }
#endif
 }

 if (hyperperiodstep>hyperperiod_size)
 {
 __po_hi_tasks_killall();
 }
 #endif
 return;
}
/*------------------------------------------------------------------------------------------------*/

void
update_sporadic_dispatch (__po_hi_task_id id_th,
                          __po_hi_local_port_t port)
{__DEBUGMSG ("0-----------***---------Sporadic dispatch after mutex th_id : %d; port_id : %d ; task type : %d -----------***---------\n\n",id_th, port, tasks_type[id_th]);
__DEBUGMSG ("Task-types : [");
for (auto i : tasks_type){
     __DEBUGMSG ("%d,", i);
}
__DEBUGMSG ("]\n\n");

#ifdef MONITORING
 if (!destroyed && (tasks_type[id_th] == __TRACE_SPORADIC_TASK_MONITORED))
  {
   __DEBUGMSG ("0-1-----------***---------Sporadic dispatch after mutex th_id : %d; port_id : %d -----------***---------\n\n",id_th, port);
  std::lock_guard<std::mutex> lock(f_i_mutex);
  modified_copy = new state_type{global_trace->back()};

 __DEBUGMSG ("1-----------***---------Sporadic dispatch after mutex th_id : %d; port_id : %d -----------***---------\n\n",id_th, port);

if (
  (__po_hi_gqueue_get_port_size((__po_hi_task_id)id_th,(__po_hi_local_port_t)port) ==    (__po_hi_int8_t)__PO_HI_GQUEUE_FIFO_INDATA
  ) &&
    (global_n_dest[id_th][port] == (__po_hi_int8_t)0)
    &&
    (po_hi_gqueues_queue_is_empty(id_th)==(__po_hi_int8_t)0)
    )
    {
monitored_port_value = __po_hi_gqueues_get_request(id_th, port);
 __DEBUGMSG ("2-----------***---------Sporadic dispatch after mutex th_id : %d; port_id : %d -----------***---------\n\n",id_th, port);

set_state_port_value(id_th, port, monitored_port_value, modified_copy);
}
 __DEBUGMSG ("3-----------***---------Sporadic dispatch after mutex th_id : %d; port_id : %d -----------***---------\n\n",id_th, port);


   hyperperiodstep++;
   modified_copy->step()=hyperperiodstep;
   modified_copy->thread_event()=id_th;
   modified_copy->port_event()=port;
//   modified_copy->port_event()=;
__DEBUGMSG ("4-----------***---------Sporadic dispatch after mutex th_id : %d; port_id : %d -----------***---------\n\n",id_th, port);
//   display_trace_temp(global_trace);

display_state_temp(modified_copy);
__DEBUGMSG ("5-----------***---------Sporadic dispatch after mutex th_id : %d; port_id : %d -----------***---------\n\n",id_th, port);

  global_trace->push(std::move(*modified_copy));
  //__DEBUGMSG ("Update_dispatch. New job Th: %d Po: %d trace size: %d\n",id_th,port_id, global_trace->stack_size());
#ifdef TRACESIZE
  if ( global_trace->stack_size()%1 == 0)
  //00 == 0)
  { //display_trace_temp(global_trace);
  int test = global_trace->back().my_size();
  __DEBUGMSG ("TRACE Total size-> stack length : %d, request_size : %d, test : %d total : %d\n", global_trace->stack_size(), sizeof(__po_hi_request_t),test,((global_trace->stack_size())*test));
  }
#endif
 }

 if (hyperperiodstep>hyperperiod_size)
 {
 __po_hi_tasks_killall();
 }

#endif
return;
}
/*------------------------------------------------------------------------------------------------*/

void trace_initialize(){

#ifdef MONITORING

__DEBUGMSG ("End of first initialization\n");

/** Allocation of ports and value to init_state **/
 memset(static_initial_state, 4242, __PO_HI_NB_PORTS*sizeof(__po_hi_request_t));

/** Initialization array **/
int i;
for (i=0; i<__PO_HI_NB_PORTS; i++){
 static_initial_state[i].port = constant_out_identifier;
}

/** Trace instanciation **/
  new_trace((step_type)0,(hyperperiod_type)0,(__po_hi_request_t*)static_initial_state);
  display_trace_temp(global_trace);

__DEBUGMSG ("End of first initialization\n");


#else
return;
#endif
}


//
//#include <stdio.h>
#ifdef __cplusplus
//#include <c_interfaces.hh>
#include <remote_configuration.hh>
#endif // __cplusplus
#include <deployment.h>


#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

#define __TRACE_GENERIC_TASK_MONITORED        0
#define __TRACE_PERIODIC_TASK_MONITORED       1
#define __TRACE_SPORADIC_TASK_MONITORED       2

/*-------------------------------------New interface----------------------------------------------*/

void update_periodic_dispatch (__po_hi_task_id id_th);

void generic_task_creation(const __po_hi_task_id      id);

void periodic_task_creation(const __po_hi_task_id      id);

void sporadic_task_creation(const __po_hi_task_id      id);

/*------------------------------------------------------------------------------------------------*/
  /*
   * Function called during each po_hi_wait_for_next_period.
   * has the charge to create new state with data port values
   * at dispatch
   */
   
void entry_ports_monitoring_at_periodic_dispatch (__po_hi_task_id id_th);

  /*
   * Function called during each po_hi_wait_for_next_period.
   * has the charge to create new state with data port values
   * at dispatch
   */

void 
update_sporadic_dispatch (__po_hi_task_id id_th, 
                          __po_hi_local_port_t port);



/*-------------------------------------Old interface----------------------------------------------*/
/*------------------------------------------------------------------------------------------------*/
//void entry_ports_wiring (__po_hi_task_id id_th, const __po_hi_uint8_t* __po_hi_n_dest);

/*------------------------------------------------------------------------------------------------*/
void trace_initialize();

/*------------------------------------------------------------------------------------------------*/
//void update_runtime (__po_hi_task_id id_th, __po_hi_local_port_t id_port, __po_hi_request_t* request);

//void
//display_trace_temp(const trace_type* trace);

/*------------------------------------------------------------------------------------------------*/
void init_monitored_ports_for_thread(__po_hi_task_id id_th, __po_hi_uint8_t* __po_hi_n_dest, int nb_ports);


//void
//delta_test();

#ifdef __cplusplus
}
#endif // __cplusplus

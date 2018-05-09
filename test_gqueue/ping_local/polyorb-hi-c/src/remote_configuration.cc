#include <iostream>

//#include <trace_interfaces.hh>
#include <meta.hh>
#include <request.h>
#include <state.hh>
#include <trace.hh>
#include <remote_configuration.hh>
#include <iterator>
#include <po_hi_debug.h>

/*****Includes to iterate on state values *****/
#include <boost/multi_index_container.hpp>
#include <boost/multi_index/hashed_index.hpp>
#include <boost/multi_index/identity.hpp>
#include <boost/multi_index/sequenced_index.hpp>


/*----------------------------------------------------------------------------*/
__po_hi_uint8_t* all_ports[__PO_HI_NB_TASKS];
__po_hi_uint8_t nb_in_ports[__PO_HI_NB_TASKS];



/*----------------------------------------------------------------------------*/


void
display_trace_temp(const trace_type* trace)
{
__DEBUGMSG ("---------------------Display Start---------------------\n");
//trace_iterator_type* ite = &new trace_iterator_type;
/*  for (const auto& state : *trace)
  {

//  const auto& state = trace->back();
      std::cout << "[step=" << state.step() << ", hyperperiod=" << state.hyperperiod() << ", thread=" << state.thread_event() << ", port=" << state.port_event() << "]\n";
    for (int i = 0 ; i<__PO_HI_NB_PORTS ; i++)
    {
      auto const& request = state.ports(i);
      std::cout << "port n : " << (__po_hi_port_t)i << " => " ;
      switch (request.port)
      {
      // >>> TO GENERATE FOR EACH PORT in ENUM __po_hi_port_t
DISPLAY_GENERATION
      // <<< END TO GENERATE

	case constant_out_identifier:
          std::cout << "Port is empty";
          break;

	case invalid_port_t:
          std::cout << "Port is invalid";
          break;

        default :
        assert(true
	    && "Should not be here -- display");
//	    (request.port < invalid_port_t ||
//	      request.port > constant_out_identifier ||
//	      request.port == (constant_out_identifier-1))
      }
//      ++requests;
      std::cout << ", \n";
    }
    std::cout << "\n";
  }
  __DEBUGMSG ("-----------------------Display End-----------------------\n");
//  destroy_trace_iterator(ite);*/
}





void
display_state_temp(const state_type* state)
{
__DEBUGMSG ("---------------------Display state Start---------------------\n");
 // trace_iterator_type* ite = new_trace_iterator(trace);
//  for (const auto& state : *trace)
  {

//  const auto& state = trace->back();
      std::cout << "[step=" << state->step() << ", hyperperiod=" << state->hyperperiod() << ", thread=" << state->thread_event() << ", port=" << state->port_event() << "]\n";
    for (int i = 0 ; i<__PO_HI_NB_PORTS ; i++)
    {
      auto const& request = state->ports(i);
      std::cout << "port n : " << (__po_hi_port_t)i << " => " ;
      switch (request.port)
      {
      // >>> TO GENERATE FOR EACH PORT in ENUM __po_hi_port_t

#ifdef PC
    case producer_global_data_source:
     std::cout << request.vars.producer_global_data_source.producer_global_data_source;
     break;

    case result_consumer_global_data_sink:
      std::cout << request.vars.result_consumer_global_data_sink.result_consumer_global_data_sink;
      break;

    case consumer_global_data_sink:
      std::cout << request.vars.consumer_global_data_sink.consumer_global_data_sink;
      break;

    case result_producer_global_data_source:
      std::cout << request.vars.result_producer_global_data_source.result_producer_global_data_source;
      break;
#elif MGMT
 	case sensor_sim_global_aoa : /* 0 */
	std::cout << request.vars.sensor_sim_global_aoa.sensor_sim_global_aoa;
break;

	case sensor_sim_global_climb_rate: /* 1 */
	std::cout << request.vars.sensor_sim_global_climb_rate.sensor_sim_global_climb_rate;
break;

	case sensor_sim_global_engine_failure: /* 2 */
	std::cout << request.vars.sensor_sim_global_engine_failure.sensor_sim_global_engine_failure;
break;

	case stall_monitor_global_aoa: /* 3 */
	std::cout << request.vars.stall_monitor_global_aoa.stall_monitor_global_aoa;
break;

	case stall_monitor_global_climb_rate: /* 4 */
	std::cout << request.vars.stall_monitor_global_climb_rate.stall_monitor_global_climb_rate;
break;

	case stall_monitor_global_stall_warn: /* 5 */
	std::cout << request.vars.stall_monitor_global_stall_warn.stall_monitor_global_stall_warn;
break;

	case hci_global_stall_warning: /* 6 */
	std::cout << request.vars.hci_global_stall_warning.hci_global_stall_warning;
break;

	case hci_global_engine_failure: /* 7 */
	std::cout << request.vars.hci_global_engine_failure.hci_global_engine_failure;
break;

	case hci_global_gear_cmd: /* 8 */
	std::cout << request.vars.hci_global_gear_cmd.hci_global_gear_cmd;
break;

	case hci_global_gear_req: /* 9 */
	std::cout << request.vars.hci_global_gear_req.hci_global_gear_req;
break;

	case hci_global_gear_ack: /* 10 */
	std::cout << request.vars.hci_global_gear_ack.hci_global_gear_ack;
break;

	case landing_gear_global_req: /* 11 */
	std::cout << request.vars.landing_gear_global_req.landing_gear_global_req;
break;

	case landing_gear_global_ack: /* 12 */
	std::cout << request.vars.landing_gear_global_ack.landing_gear_global_ack;
break;

	case landing_gear_global_dummy_out: /* 13 */
	std::cout << request.vars.landing_gear_global_dummy_out.landing_gear_global_dummy_out;
break;

	case landing_gear_global_dummy_in: /* 14 */
	std::cout << request.vars.landing_gear_global_dummy_in.landing_gear_global_dummy_in;
break;

	caseoperator_global_gear_cmd: /* 15 */
	std::cout << request.vars.operator_global_gear_cmd.operator_global_gear_cmd;
#endif
// <<< END TO GENERATE


      // <<< END TO GENERATE

	case constant_out_identifier:
          std::cout << "Port is empty";
          break;

	case invalid_port_t:
          std::cout << "Port is invalid";
          break;

        default :
        assert(true
	    && "Should not be here -- display");
//	    (request.port < invalid_port_t ||
//	      request.port > constant_out_identifier ||
//	      request.port == (constant_out_identifier-1))
      }
//      ++requests;
      std::cout << ", \n";
    }
    std::cout << "\n";
  }
  __DEBUGMSG ("-----------------------Display state End-----------------------\n");
//  destroy_trace_iterator(ite);*/
}



//} // extern "C"




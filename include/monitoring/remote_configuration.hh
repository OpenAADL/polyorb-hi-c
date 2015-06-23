#pragma once


#include <meta.hh>
#include <request.h>
#include <state.hh>
#include <trace.hh>
#include <deployment.h>


// Parameter i in the template parameters list
// gives the number of ports for thread i.
// >>> TO GENERATE
using ports_type = taste::ports_table< __PO_HI_PORT_TYPE_CONTENT >;
// <<< END TO GENERATE
using state_type = taste::state<__po_hi_request_t, ports_type>;
using trace_type = taste::trace<state_type>;
//using monitoring_type = taste::state<int, ports_type>;

extern "C" {
void
display_trace_temp(const trace_type* trace);
}

extern "C" {
void
display_state_temp(const state_type* state);
}

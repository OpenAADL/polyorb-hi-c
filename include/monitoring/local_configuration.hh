#pragma once

#include <iosfwd>

#include "meta.hh"
#include "request.h"
#include "state.hh"
#include "trace.hh"

/*------------------------------------------------------------------------------------------------*/

// Parameter i in the template parameters list gives the number of ports for thread i.
// >>> TO GENERATE
using ports_type = taste::ports_table<1, 1>;
// <<< END TO GENERATE
using state_type = taste::state<__po_hi_request_t, ports_type>;
using trace_type = taste::trace<state_type>;

/*------------------------------------------------------------------------------------------------*/

inline // < Don't forget!
bool
operator==(const __po_hi_request_t& lhs, const __po_hi_request_t& rhs)
noexcept
{
  if (lhs.port != rhs.port)
  {
    return false;
  }

  // lhs and rhs have the same port, it's OK to switch on the port of any of them.
  switch (lhs.port)
  {

// >>> TO GENERATE FOR EACH PORT in ENUM __po_hi_port_t
    case producer_global_data_source:
      return lhs.vars.producer_global_data_source.producer_global_data_source
          == rhs.vars.producer_global_data_source.producer_global_data_source;

    case result_consumer_global_data_sink:
      return lhs.vars.result_consumer_global_data_sink.result_consumer_global_data_sink
          == rhs.vars.result_consumer_global_data_sink.result_consumer_global_data_sink;

    case consumer_global_data_sink:
      return lhs.vars.consumer_global_data_sink.consumer_global_data_sink
          == rhs.vars.consumer_global_data_sink.consumer_global_data_sink;

    case result_producer_global_data_source:
      return lhs.vars.result_producer_global_data_source.result_producer_global_data_source
          == rhs.vars.result_producer_global_data_source.result_producer_global_data_source;
// <<< END TO GENERATE

    default:
      assert(false && "Should not be here");
      __builtin_unreachable();
  }
}

/*------------------------------------------------------------------------------------------------*/

namespace std {

template <>
struct hash <__po_hi_request_t>
{
  std::size_t
  operator()(const __po_hi_request_t& r)
  const noexcept
  {
    // We need to know the underlying type of the port enum. Then, we can cast to this type
    // and use the value of the enum to compute its hash value.
    using ty = std::underlying_type_t<__po_hi_port_t>;
    auto seed = std::hash<ty>()(static_cast<ty>(r.port));
    switch (r.port)
    {

// >>> TO GENERATE FOR EACH PORT in ENUM __po_hi_port_t
      case producer_global_data_source:
        taste::hash_combine(seed, r.vars.producer_global_data_source.producer_global_data_source);
        break;

      case result_consumer_global_data_sink:
        taste::hash_combine(seed, r.vars.result_consumer_global_data_sink.result_consumer_global_data_sink);
        break;

      case consumer_global_data_sink:
        taste::hash_combine(seed, r.vars.consumer_global_data_sink.consumer_global_data_sink);
        break;

      case result_producer_global_data_source:
        taste::hash_combine(seed, r.vars.result_producer_global_data_source.result_producer_global_data_source);
        break;
// <<< END TO GENERATE

      default:
        assert(false && "Should not be here");
    }
    return seed;
  }
};

} // namespace std

/*------------------------------------------------------------------------------------------------*/

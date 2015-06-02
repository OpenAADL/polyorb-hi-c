#pragma once

#include <algorithm> // copy, equal
#include <array>
#include <cassert>
#include <iosfwd>
#include <iterator>
#include <memory>    // unique_ptr

#include <boost/python.hpp>


namespace taste {

/*----------------------------------------------------------------------------*/

template <int tasks>
class schedule
{
public:

  static_assert(tasks > 0, "The number of scheduling states must be over 0.");

private:

  struct scheduling_data_type
  {
    unsigned int hyperperiod_length;
    unsigned int task_name_matching;

    
    // Should we share this amongst all states?
   /* array_type ports_;

    data_type() = default;
    data_type(const data_type&) = default;

    const request_type&
    port_value(std::size_t thread_id, std::size_t port_id)
    const noexcept
    {
      return ports_[Ports::jump_table[thread_id] + port_id];
    }

    request_type&
    port_value(std::size_t thread_id, std::size_t port_id)
    noexcept
    {
      return ports_[Ports::jump_table[thread_id] + port_id];
    }
  };
*/
  std::unique_ptr<scheduling_data_type> ptr_;

public:

  schedule()
    : ptr_{std::make_unique<scheduling_data_type>()}
  {}

  schedule(const state& other)
    : ptr_{std::make_unique<scheduling_data_type>(*other.ptr_)} // deep copy
  {}

  state&
  operator=(const state& other)
  {
    if (this != &other)
    {
      ptr_ = std::make_unique<data_type>(*other.ptr_); // deep copy
    }
    return *this;
  }

  state(state&&) = default;
  state& operator=(state&&) = default;

  const request_type&
  port_value(std::size_t thread_id, std::size_t port_id)
  const noexcept
  {
    assert(thread_id < Ports::nb_threads && "Incorrect thread id");
    assert(port_id < Ports::ports_for_thread[thread_id] && "Incorrect port id for this thread id");
    return ptr_->port_value(thread_id, port_id);
  }

  request_type&
  port_value(std::size_t thread_id, std::size_t port_id)
  noexcept
  {
    assert(thread_id < Ports::nb_threads && "Incorrect thread id");
    assert(port_id < Ports::ports_for_thread[thread_id] && "Incorrect port id for this thread id");
    return ptr_->port_value(thread_id, port_id);
  }

  step_type
  step()
  const noexcept
  {
    return ptr_->step_;
  }

  step_type&
  step()
  noexcept
  {
    return ptr_->step_;
  }

  hyperperiod_type
  hyperperiod()
  const noexcept
  {
    return ptr_->hyperperiod_;
  }

  hyperperiod_type&
  hyperperiod()
  noexcept
  {
    return ptr_->hyperperiod_;
  }
  
  thread_event_type
  thread_event()
  const noexcept
  {
    return ptr_->thread_event_;
  }

  thread_event_type&
  thread_event()
  noexcept
  {
    return ptr_->thread_event_;
  }
  
  port_event_type
  port_event()
  const noexcept
  {
    return ptr_->port_event_;
  }

  port_event_type&
  port_event()
  noexcept
  {
    return ptr_->port_event_;
  }

  const char*
  ports_data()
  const noexcept
  {
    return reinterpret_cast<const char*>(ptr_->ports_.data());
  }

  const request_type&
  ports(int index)
  const noexcept
  {
    return ptr_->ports_[index];
  }

  static int 
  my_size()
  { int i = (sizeof(port_event_type) + sizeof(thread_event_type) + sizeof(hyperperiod_type) + sizeof(step_type));
//   printf ("Progress report display, will be removed: port_event %d, thread_event %d,hpp_occ %d,hpp_step %d,\n",sizeof(port_event_type), sizeof(thread_event_type), sizeof(hyperperiod_type), sizeof(step_type));
//    printf ("Progress report display, will be removed: request size %d, constant size %d\n\n*****************************************************************************************************\n", sizeof(request_type),i);
    return ports_size*sizeof(request_type) + sizeof(port_event_type) + sizeof(thread_event_type) + sizeof(hyperperiod_type) + sizeof(step_type);
  }

  friend
  bool
  operator==(const state& lhs, const state& rhs)
  noexcept
  {
    // Highly dangerous : we directly comparing memory contents, thus relying on correct
    // initialization (to 0) of the underlying data.
    return lhs.step() == rhs.step() and lhs.hyperperiod() == rhs.hyperperiod()
         and std::equal(lhs.ports_data(), lhs.ports_data() + ports_size, rhs.ports_data());
  }
};

/*------------------------------------------------------------------------------------------------*/

} // namespace taste


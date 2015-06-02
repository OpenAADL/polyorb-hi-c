#pragma once

#include <iosfwd>

#pragma GCC diagnostic push
#if defined(__GNUC__) && !defined(__clang__)
# pragma GCC diagnostic ignored "-Wunused-local-typedefs"
#endif
#include <boost/multi_index_container.hpp>
#include <boost/multi_index/hashed_index.hpp>
#include <boost/multi_index/identity.hpp>
#include <boost/multi_index/sequenced_index.hpp>
#pragma GCC diagnostic pop

#include "state.hh"

namespace taste {

/*------------------------------------------------------------------------------------------------*/

namespace bmi = boost::multi_index;

/*------------------------------------------------------------------------------------------------*/

template <typename State>
class trace
{
public:

  /// @brief The type of a state stored by this trace.
  using state_type = State;

private:


  /// @brief A tag to identify the view ordered by insertion order for boost::multi_index.
  struct insertion_order{};

  /// @brief A type that keeps order of insertion and ensures that states are stored only once.
  using stack_type =
    bmi::multi_index_container< state_type
                              , bmi::indexed_by< bmi::sequenced<bmi::tag<insertion_order>>
                                               , bmi::hashed_unique< bmi::identity<state_type>
                                                                   , std::hash<state_type>
                                                                   >
                                               >>;

  /// @brief The type of the stack when viewed with its insertion order.
  using ordered_stack_type = typename stack_type::template index<insertion_order>::type;

  /// @brief Stores states with a LIFO data structure.
  stack_type stack_;

public:

  /// @brief The type of an iterator on a trace.
  using const_iterator = typename ordered_stack_type::const_iterator;

  /// @brief The type of an iterator on a trace.
  using const_reverse_iterator = typename ordered_stack_type::const_reverse_iterator;

  trace() = default;

  trace(const trace&) = delete;
  trace& operator=(const trace&) = delete;

  trace(trace&&) = default;
  trace& operator=(trace&&) = default;

  /// @brief Pushes a new state to the trace.
  /// @return True if the state already exists in the stack, false otherwise.
  bool
  push(state_type&& s)
  {
    const auto insertion = stack().push_back(std::move(s));
    return not insertion.second;
  }

  /// @brief Pops the last pushed state.
  void
  pop()
  {
    stack().pop_back();
  }

  const state_type&
  back()
  const noexcept
  {
    return stack().back();
  }

  const_iterator
  begin()
  const noexcept
  {
    return stack().begin();
  }

  const_iterator
  end()
  const noexcept
  {
    return stack().end();
  }

  const_reverse_iterator
  rbegin()
  const noexcept
  {
    return stack().rbegin();
  }

  const_reverse_iterator
  rend()
  const noexcept
  {
    return stack().rend();
  }

  auto
  stack_size()
  noexcept
  {
    return stack_.size();
  }

private:

  ordered_stack_type&
  stack()
  noexcept
  {
    return stack_.template get<insertion_order>();
  }

  const ordered_stack_type&
  stack()
  const noexcept
  {
    return stack_.template get<insertion_order>();
  }
};

/*------------------------------------------------------------------------------------------------*/

} // namespace taste

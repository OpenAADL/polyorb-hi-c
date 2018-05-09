#pragma once

#include <array>
#include <utility>  // integer_sequence
#include <tuple>

namespace taste {

/*----------------------------------------------------------------------------*/

template <std::size_t X, std::size_t... Xs>
struct sum
{
  static constexpr auto value = X + sum<Xs...>::value;
};

template <std::size_t X>
struct sum<X>
{
  static constexpr auto value = X;
};

/*----------------------------------------------------------------------------*/

template <std::size_t Acc, std::size_t X, std::size_t... Xs>
struct accumulate
{
  static constexpr auto recursion = accumulate<Acc + X, Xs...>::value;
  static constexpr auto value = std::tuple_cat(std::make_tuple(Acc), recursion);
};

template <std::size_t Acc, std::size_t X>
struct accumulate<Acc, X>
{
  static constexpr auto value = std::make_tuple(Acc);
};

/*----------------------------------------------------------------------------*/

template <typename Tuple, std::size_t... Indices>
constexpr
std::array<std::size_t, std::tuple_size<Tuple>::value>
tuple_to_array(const Tuple& t, std::index_sequence<Indices...>)
{
  return {{std::get<Indices>(t)...}};
}

/*----------------------------------------------------------------------------*/

template <std::size_t... Ports>
struct ports_table
{
  // For assertion purposes.
  static constexpr auto nb_threads = sizeof...(Ports);
  static constexpr std::size_t ports_for_thread[] = {Ports...};

  static constexpr auto size = sum<Ports...>::value;

  static constexpr auto tuple = accumulate<0, Ports...>::value;
  static constexpr auto tuple_size = std::tuple_size<decltype(tuple)>::value;

  using jump_table_type = decltype(tuple_to_array(tuple, std::make_index_sequence<tuple_size>()));
  static constexpr jump_table_type jump_table
    = tuple_to_array(tuple, std::make_index_sequence<tuple_size>());
};

// Definition of ports.
template<std::size_t... Ports>
constexpr std::size_t ports_table<Ports...>::ports_for_thread[];

// Definition of jump_table.
template<std::size_t... Ports>
typename ports_table<Ports...>::jump_table_type constexpr ports_table<Ports...>::jump_table;

/*----------------------------------------------------------------------------*/

} // namespace taste

#pragma once

#include <algorithm> // for_each

namespace taste {

/*------------------------------------------------------------------------------------------------*/

template <typename T>
inline
void
hash_combine(std::size_t& seed, const T& x)
noexcept(noexcept(std::hash<T>()(x)))
{
  seed ^= std::hash<T>()(x) + 0x9e3779b9 + (seed<<6) + (seed>>2);
}

/*------------------------------------------------------------------------------------------------*/

/// @brief Hash a range.
template <typename InputIterator>
inline
void
hash_combine(std::size_t& seed, InputIterator cit, InputIterator cend)
{
  std::for_each(cit, cend, [&](const auto& v){hash_combine(seed, v);});
}

/*------------------------------------------------------------------------------------------------*/

} // namespace taste

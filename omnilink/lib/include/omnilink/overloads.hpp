#pragma once

namespace omnilink {

// https://en.cppreference.com/w/cpp/utility/variant/visit
template <class... Ts> struct overloads : Ts... {
  using Ts::operator()...;
};

} // namespace omnilink

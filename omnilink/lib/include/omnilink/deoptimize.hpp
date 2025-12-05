#pragma once

namespace omnilink {

template <typename T> inline void deoptimize(T *t) {
  using F = void (*)(T *);
  // By my experimentation, the volatile qualifier requires
  // the compiler to behave as-if fn might be any function,
  // not just the do-nothing lambda it definitely holds.
  // As a result, this will ensure the T* points
  // to a real, fully formed object T (and fn is actually called with it),
  // even if it would optimize it out normally.
  volatile F fn = [](T *) -> void { return; };
  fn(t);
}

} // namespace omnilink

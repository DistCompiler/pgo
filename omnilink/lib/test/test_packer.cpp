#include <cstdlib>
#include <iostream>
#include <map>
#include <msgpack.hpp>
#include <omnilink/pack.hpp>
#include <sstream>

using omnilink::Packable;

template <typename P> static std::string mp(const P &packable) {
  std::ostringstream out;
  msgpack::pack(out, packable);
  return out.str();
}

template <typename P> static std::string mp_P(const P &packable) {
  std::ostringstream out;
  Packable p = packable;
  msgpack::pack(out, p);
  return out.str();
}

template <typename P> static void compare_packs(const P &packable) {
  auto r = mp(packable);
  auto r_P = mp_P(packable);

  if (r != r_P) {
    std::cerr << "Mismatch between packed objects: " << r << " vs " << r_P
              << std::endl;
    std::abort();
  }
}

int main() {
  compare_packs(42);
  compare_packs(std::map<std::string, int>{{"foo", 42}, {"bar", 96}});
  return 0;
}

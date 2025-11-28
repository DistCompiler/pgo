#pragma once

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <iterator>
#include <omnilink/overloads.hpp>

#include <array>
#include <variant>
#include <vector>

#include <msgpack.hpp>

#include <iostream>

namespace omnilink {

static constexpr std::size_t small_buf_size = 256;

struct Packable {
  Packable() : Packable{msgpack::object{}} {}

  template <typename T> Packable(const T &value) { setFrom(value); }

  template <typename T> Packable &operator=(const T &value) {
    setFrom(value);
    return *this;
  }

  template <typename Stream>
  msgpack::packer<Stream> &pack(msgpack::packer<Stream> &packer) const {
    // Pack our pre-rendered msgpack as a body without its length deliberately.
    // This _should_ basically just splice the msgpack data into a larger
    // message.
    std::visit([&](auto &impl) { impl.pack(packer); }, bytes.impl);
    return packer;
  }

private:
  template <typename T> void setFrom(const T &value) {
    bytes = {noalloc_t{}};
    msgpack::pack(bytes, value);
  }

  using buf_t = std::array<char, small_buf_size>;
  struct alloc_t {
    buf_t buf;
    std::vector<char> rest;

    void write(const char *data, std::size_t count) {
      std::copy(data, data + count, std::back_insert_iterator(rest));
    }

    template <typename Stream>
    msgpack::packer<Stream> &pack(msgpack::packer<Stream> &packer) const {
      packer.pack_bin_body(buf.data(), buf.size());
      packer.pack_bin_body(rest.data(), rest.size());
      return packer;
    }

    static alloc_t from_noalloc(buf_t &buf) { return alloc_t{buf}; }

  private:
    alloc_t(const buf_t &buf) : buf{buf} {}
  };
  struct noalloc_t {
    buf_t buf;
    std::size_t len = 0;

    std::size_t cap_remaining() const { return small_buf_size - len; }

    void write(const char *data, std::size_t count) {
      assert(count <= cap_remaining());
      std::copy(data, data + count, buf.begin() + len);
      len += count;
    }

    template <typename Stream>
    msgpack::packer<Stream> &pack(msgpack::packer<Stream> &packer) const {
      packer.pack_bin_body(buf.data(), len);
      return packer;
    }
  };

  struct bytes_t {
    void write(const char *data, std::size_t count) {
      struct {
        const char *data;
        std::size_t count;
        std::variant<noalloc_t, alloc_t> &self_impl;

        void operator()(noalloc_t &impl) {
          if (count <= impl.cap_remaining()) {
            impl.write(data, count);
          } else {
            std::size_t c_short = impl.cap_remaining();
            impl.write(data, c_short);
            alloc_t alloc = alloc_t::from_noalloc(impl.buf);
            alloc.write(data + c_short, count - c_short);
            self_impl = alloc;
          }
        }
        void operator()(alloc_t &impl) { impl.write(data, count); }
      } visitor{data, count, impl};
      std::visit(visitor, impl);
    }
    std::variant<noalloc_t, alloc_t> impl = noalloc_t{};
  } bytes;
};

} // namespace omnilink

namespace msgpack::adaptor {

template <typename... Variants> struct pack<std::variant<Variants...>> {
  template <typename Stream>
  msgpack::packer<Stream> &
  operator()(msgpack::packer<Stream> &packer,
             std::variant<Variants...> const &v) const {
    return std::visit(
        [&](const auto &var) -> decltype(packer) { return packer.pack(var); },
        v);
  }
};

#if __cplusplus >= 202002L

template <typename T, std::size_t extent> struct pack<std::span<T, extent>> {
  template <typename Stream>
  msgpack::packer<Stream> &operator()(msgpack::packer<Stream> &packer,
                                      std::span<T, extent> span) const {
    packer.pack_array(span.size());
    for (const auto &elem : span) {
      packer.pack(elem);
    }
    return packer;
  }
};

#endif

template <> struct pack<omnilink::Packable> {
  template <typename Stream>
  msgpack::packer<Stream> &operator()(msgpack::packer<Stream> &packer,
                                      const omnilink::Packable &v) const {
    return v.pack(packer);
  }
};

template <> struct convert<omnilink::Packable> {
  msgpack::object const &operator()(msgpack::object const &obj,
                                    omnilink::Packable &v) const {
    v = obj;
    return obj;
  }
};

} // namespace msgpack::adaptor

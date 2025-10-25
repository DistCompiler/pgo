#pragma once

#include <variant>

#include <msgpack.hpp>

namespace omnilink {

struct Packable {
    Packable() : Packable{msgpack::object{}} {}

    template<typename T>
    Packable(const T& value) {
        setFrom(value);
    }

    template<typename T>
    Packable& operator=(const T& value) {
        setFrom(value);
        return *this;
    }

    template<typename Stream>
    msgpack::packer<Stream>& pack(msgpack::packer<Stream>& packer) const {
        // Pack our pre-rendered msgpack as a body without its length deliberately.
        // This _should_ basically just splice the msgpack data into a larger message.
        packer.pack_bin_body(bytes.c_str(), bytes.size());
        return packer;
    }
private:
    template<typename T>
    void setFrom(const T& value) {
        std::ostringstream out;
        msgpack::pack(out, value);
        bytes = out.str();
    }

    std::string bytes;
};

} // omnilink

namespace msgpack::adaptor {

template <typename ...Variants>
struct pack<std::variant<Variants...>> {
    template <typename Stream>
    msgpack::packer<Stream>& operator()(msgpack::packer<Stream>& packer, std::variant<Variants...> const& v) const {
        return std::visit([&](const auto& var) -> decltype(packer) {
            return packer.pack(var);
        }, v);
    }
};

template <>
struct pack<omnilink::Packable> {
    template <typename Stream>
    msgpack::packer<Stream>& operator()(msgpack::packer<Stream>& packer, const omnilink::Packable& v) const {
        return v.pack(packer);
    }
};

template <>
struct convert<omnilink::Packable> {
    msgpack::object const& operator()(msgpack::object const& obj, omnilink::Packable& v) const {
        v = obj;
        return obj;
    }
};

} // msgpack::adaptor

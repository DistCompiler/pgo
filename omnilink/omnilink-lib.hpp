#pragma once

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <stdexcept>
#include <string_view>
#include <variant>
#include <filesystem>
#include <functional>
#include <initializer_list>
#include <limits>
#include <memory>
#include <msgpack/v3/object_decl.hpp>
#include <sstream>
#include <vector>
#include <thread>
#include <string>
#include <fstream>
#include <random>
#include <iostream>

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

namespace omnilink {

template<typename T>
struct Tag {};

struct UnsupportedException {};

template<typename _Self, typename _WorkloadContext, typename AnyOperation>
struct RunnerDefns {
    static_assert(false, "AnyOperation must be a variant of operation structs");
};

template<typename _Self, typename _WorkloadContext, typename ...Operations>
struct RunnerDefns<_Self, _WorkloadContext, std::variant<Operations...>> {
    using WorkloadContext = _WorkloadContext;
    using Self = RunnerDefns<_Self, WorkloadContext, std::variant<Operations...>>;

    WorkloadContext& workload_context;
    const std::size_t thread_idx;

    RunnerDefns(WorkloadContext& _workload_context, std::size_t _thread_idx) :
        workload_context{_workload_context},
        thread_idx{_thread_idx}
    {}

    RunnerDefns(const Self&) = delete;
    RunnerDefns(Self&&) = delete;

    #ifdef TRACELINK_USE_RANDOM_DEVICE
    using rand_tp = std::random_device;
    rand_tp rand{"/dev/urandom"};
    #else
    using rand_tp = std::mt19937;
    rand_tp rand{std::random_device{"/dev/urandom"}()};
    #endif

    void operator()() {
        // TODO: no-timestamp burst mode toggle
        using OpFun = void(Self::*)();
        std::initializer_list<OpFun> operations =
            {(&Self::perform_operation_wrapper<Operations>)...};
        auto uniform_idx_dist = std::uniform_int_distribution<std::size_t>(0, operations.size() - 1);

        for(std::size_t i = 0; i < workload_context.operation_count; ++i) {
            std::size_t consecutive_failures = 0;
            bool shouldTry = true;
            while(shouldTry) {
                if (consecutive_failures >= workload_context.max_consecutive_failures) {
                    std::cerr << "[thread " << thread_idx << "] "
                              << "could not choose a valid operation after "
                              << workload_context.max_consecutive_failures
                              << " attempts! Exiting early at iteration "
                              << i
                              << " rather than risk an infinite loop."
                              << std::endl;
                    goto end_of_workload;
                }
                shouldTry = false;
                try {
                    std::size_t idx = uniform_idx_dist(rand);

                    auto it = std::begin(operations);
                    std::advance(it, idx);
                    (this->*(*it))();
                } catch (UnsupportedException&) {
                    shouldTry = true;
                    ++consecutive_failures;
                }
            }
        }
        end_of_workload: {
            std::cout << "end of workload " << thread_idx << std::endl;
        }
    }

private:
    using AnyOperation = std::variant<Operations...>;
    struct ActionRecord {
        // TLC can't handle bigger than int32
        int32_t op_start, op_end;
        std::string_view operation_name;
        AnyOperation operation;
        bool should_succeed;
        MSGPACK_DEFINE_MAP(op_start, op_end, operation_name, operation, should_succeed);
    };

    std::ofstream log_out = std::ofstream(workload_context.logs_dir / log_filename(), std::ios::binary);

    std::string log_filename() const {
        std::ostringstream out;
        out << "tracing-";
        out << thread_idx;
        out << ".log";
        return out.str();
    }

    constexpr _Self& self() {
        return static_cast<_Self&>(*this);
    }

    template<typename Operation>
    void perform_operation_wrapper() {
        auto& w = self().workload_context;
        auto op_start = w.get_timestamp_now() - w.init_timestamp;
        Operation result = self().perform_operation(Tag<Operation>{});
        auto op_end = w.get_timestamp_now() - w.init_timestamp;

        if (op_start >= std::numeric_limits<int32_t>::max())
            throw omnilink::UnsupportedException{};
        if (op_end >= std::numeric_limits<int32_t>::max())
            throw omnilink::UnsupportedException{};

        bool should_succeed = !result._did_abort;

        msgpack::pack(log_out, ActionRecord{
            static_cast<int32_t>(op_start),
            static_cast<int32_t>(op_end),
            Operation::_name_,
            result,
            should_succeed,
        });
        log_out.flush();
    }
};

template<typename _Self, typename AnyOperation>
struct WorkloadContext {
    template<typename _RunnerDefns>
    using RunnerDefnsBase = RunnerDefns<_RunnerDefns, _Self, AnyOperation>;

    const std::filesystem::path logs_dir = std::filesystem::current_path();
    const std::size_t operation_count = env_opt("OMNILINK_OPERATIONS");
    const std::size_t thread_count = env_opt("OMNILINK_THREADS");
    const uint64_t init_timestamp = get_timestamp_now();
    const std::size_t max_consecutive_failures = env_opt("OMNILINK_CONSECUTIVE_FAILURES", 1000);

    static uint64_t rdtsc() {
        unsigned int lo,hi;
        __asm__ __volatile__ ("rdtsc" : "=a" (lo), "=d" (hi));
        return (((uint64_t)(hi & ~(1<<31)) << 32) | lo);
    }

    uint64_t get_timestamp_now() const {
        // using namespace std::chrono_literals;
        // return std::chrono::high_resolution_clock::now().time_since_epoch() / 1ns;
        // this is a stable counter + memory fence
        return rdtsc();
    }

    // Note: if you use thread IDs, the main thread (which might own global state)
    // has thread ID 0.
    void run() {
        std::vector<std::thread> threads;
        threads.reserve(thread_count);
        for(std::size_t i = 0; i < thread_count; ++i) {
            threads.emplace_back([this, i]() {
                // Correctness: make sure defns' lifecycle is fully on the new thread.
                // Otherwise, if it uses any thread-local storage, you will see confusing
                // and impossible-seeming behavior.
                typename _Self::RunnerDefns defns{{self(), i + 1}};
                defns();
            });
        }
        for(auto& thread : threads) {
            thread.join();
        }
    }

    static int main() {
        _Self{}.run();
        return 0;
    }
private:
    constexpr _Self& self() {
        return static_cast<_Self&>(*this);
    }

    std::size_t env_opt(const char* opt_name, std::optional<std::size_t> _default = {}) {
        const char* val = std::getenv(opt_name);
        if (val) {
            return std::stoi(val);
        } else if (_default.has_value()) {
            return _default.value();
        } else {
            std::ostringstream out;
            out << "Couldn't guess thread count because " << opt_name << " wasn't set";
            throw std::invalid_argument{out.str()};
        }
    }
};

} // omnilink

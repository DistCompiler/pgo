#pragma once

#include "logger.hpp"
#include <omnilink/pack.hpp>
#include <omnilink/logger.hpp>

#include <cstdint>
#include <cstdlib>
#include <stdexcept>
#include <string_view>
#include <variant>
#include <initializer_list>
#include <sstream>
#include <vector>
#include <thread>
#include <string>
#include <random>
#include <iostream>
#include <algorithm>

#include <msgpack.hpp>

namespace omnilink {

struct UnsupportedException {};

struct TerminateThread {
    static constexpr std::string_view _name_ = "__TerminateThread";
    bool _did_abort = false;
    uint64_t _op_start = 0, _op_end = 0;
    omnilink::Packable _meta;
    MSGPACK_DEFINE_MAP(_did_abort, _op_start, _op_end, _meta);
};

template<typename... Operations>
struct pretty_name_of<std::variant<TerminateThread, Operations...>> {
    static constexpr std::string_view value = pretty_name_of<std::variant<Operations...>>::value;
};

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
    rand_tp rand{std::random_device{"/dev/urandom"}() + thread_idx};
    #endif

    template<typename Operation>
    struct Ctx {
        Operation& op;
        void refine_op_start() {
            log::mark_operation_start();
        }
        void refine_op_end() {
            log::mark_operation_end();
        }
        void unsupported() {
            throw omnilink::UnsupportedException{};
        }
        friend struct RunnerDefns<_Self, _WorkloadContext, std::variant<Operations...>>;
    private:
        Ctx(_WorkloadContext& w): w{w}, op{log::template start_operation<Operation>()} {}
        _WorkloadContext& w;
    };

    void operator()() {
        // TODO: no-timestamp burst mode toggle
        using OpFun = void(Self::*)();
        std::initializer_list<OpFun> operations =
            {(&Self::perform_operation_wrapper<Operations>)...};
        auto uniform_idx_dist = std::uniform_int_distribution<std::size_t>(0, operations.size() - 1);

        for(std::size_t i = 0; i < workload_context.operation_count; ++i) {
            std::array<uint64_t, sizeof...(Operations)> consecutive_failures = {0};
            bool shouldTry = true;
            while(shouldTry) {
                auto min_consecutive_fail_it = std::min_element(std::begin(consecutive_failures), std::end(consecutive_failures));
                if (*min_consecutive_fail_it >= workload_context.max_consecutive_failures) {
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
                std::size_t idx = uniform_idx_dist(rand);
                try {
                    auto it = std::begin(operations);
                    std::advance(it, idx);
                    (this->*(*it))();
                } catch (UnsupportedException&) {
                    shouldTry = true;
                    ++consecutive_failures[idx];
                }
            }
        }
        end_of_workload: {
            // Mark the start of any cleanup ops (see: TerminateThreadData below)
            auto& op = log::template start_operation<TerminateThread>();
            self().fill_terminate_meta(op._meta);
            std::cout << "end of workload " << thread_idx << std::endl;
        }
    }

    void fill_terminate_meta(Packable& meta) {}

private:
    // TerminateThread must be 1st for pretty_name_of to work (see above)
    using AnyOperation = std::variant<TerminateThread, Operations...>;
    using log = logger<AnyOperation>;

    struct TerminateThreadSentinel {
        // When reaching this destructor, we know all subclass fields have been cleaned up.
        // Therefore, we have finished any cleanup ops our workload requires.
        ~TerminateThreadSentinel() {
            log::template end_operation<TerminateThread>();
        }
    } terminate_thread_sentinel;

    constexpr _Self& self() {
        return static_cast<_Self&>(*this);
    }

    template<typename Operation>
    void perform_operation_wrapper() {
        auto& w = self().workload_context;
        Ctx<Operation> ctx{w}; // includes start_operation
        self().perform_operation(ctx);
        log::template end_operation<Operation>();
    }
};

template<typename _Self, typename AnyOperation>
struct WorkloadContext {
    template<typename _RunnerDefns>
    using RunnerDefnsBase = RunnerDefns<_RunnerDefns, _Self, AnyOperation>;

    const std::size_t operation_count = env_opt("OMNILINK_OPERATIONS");
    const std::size_t thread_count = env_opt("OMNILINK_THREADS");
    const std::size_t max_consecutive_failures = env_opt("OMNILINK_CONSECUTIVE_FAILURES", 10000);

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

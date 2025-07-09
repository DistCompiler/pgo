#pragma once

#include <chrono>
#include <filesystem>
#include <initializer_list>
#include <sstream>
#include <vector>
#include <thread>
#include <string>
#include <fstream>
#include <random>

#include <msgpack.hpp>

#define TRACELINK_RUNNER_DEFNS_INIT(RunnerDefns)                              \
    RunnerDefns(WorkloadContext& workload_context, std::size_t thread_idx) :  \
        Self{workload_context, thread_idx}                                    \
    {}

namespace msgpack::adaptor {

template <typename ...Variants>
struct pack<std::variant<Variants...>> {
    template <typename Stream>
    msgpack::packer<Stream>& operator()(msgpack::packer<Stream>& packer, std::variant<Variants...> const& v) const {
        return std::visit([&](const auto& var) -> decltype(packer) {
            packer.pack(var);
            return packer;
        }, v);
    }
};

}

namespace tracelink {

template<typename T>
struct Tag {};

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
    RunnerDefns(Self&&) = default;

    void operator()() {
        using OpFun = void(Self::*)();
        std::initializer_list<OpFun> operations =
            {(&Self::perform_operation_wrapper<Operations>)...};
        auto uniform_idx_dist = std::uniform_int_distribution<std::size_t>(0, operations.size() - 1);

        for(std::size_t i = 0; i < workload_context.operation_count; ++i) {
            std::size_t idx = uniform_idx_dist(rand);

            auto it = std::begin(operations);
            std::advance(it, idx);
            (this->*(*it))();
        }
    }

private:
    using rand_tp = std::mt19937;
    rand_tp rand;

    using AnyOperation = std::variant<Operations...>;
    struct ActionRecord {
        std::chrono::system_clock::time_point op_start, op_end;
        std::string_view operation_name;
        AnyOperation operation;
        MSGPACK_DEFINE_MAP(op_start, op_end, operation_name, operation);
    };

    std::ofstream log_out = std::ofstream(workload_context.logs_dir / log_filename(), std::ios::binary);

    std::string log_filename() const {
        std::ostringstream out;
        out << "tracing-";
        out << thread_idx;
        out << ".log";
        return out.str();
    }

    _Self& self() {
        return static_cast<_Self&>(*this);
    }

    template<typename Operation>
    void perform_operation_wrapper() {
        auto op_start = std::chrono::system_clock::now();
        Operation result = self().perform_operation(Tag<Operation>{});
        auto op_end = std::chrono::system_clock::now();

        msgpack::pack(log_out, ActionRecord{
            op_start,
            op_end,
            Operation::_name_,
            result,
        });
        log_out.flush();
    }
};

template<typename _Self, typename AnyOperation>
struct WorkloadContext {
    template<typename _RunnerDefns>
    using RunnerDefnsBase = RunnerDefns<_RunnerDefns, _Self, AnyOperation>;

    const std::filesystem::path logs_dir = std::filesystem::current_path();
    const std::size_t operation_count = 20;
    const std::size_t thread_count = 1;

    void run() {
        std::vector<std::thread> threads;
        for(std::size_t i = 0; i < thread_count; ++i) {
            threads.push_back(std::thread(typename _Self::RunnerDefns{
                self(),
                i
            }));
        }
        for(auto& thread : threads) {
            thread.join();
        }
    }
private:
    _Self& self() {
        return static_cast<_Self&>(*this);
    }
};

} // tracelink

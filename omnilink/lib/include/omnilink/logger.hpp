#pragma once

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <unistd.h>
#include <sys/types.h>
#include <variant>
#include <atomic>

#include <msgpack.hpp>

namespace omnilink {

template<typename AnyOperation>
struct pretty_name_of {
    // static constexpr std::string_view value = "???";
};

static uint64_t get_timestamp_now() {
    // Thread local is ok, per link below.
    // This might work better from a C library, since static initialization
    // happens inside the function (and we can be called from a C library).
    static thread_local std::atomic<int> _dummy_var_for_mfence = 0;
    unsigned int lo,hi;
    _dummy_var_for_mfence.exchange(1); // prevent CPU reorderings
    // potentially faster than std::atomic_thread_fence https://stackoverflow.com/questions/48316830/why-does-this-stdatomic-thread-fence-work
    __asm__ __volatile__ ("rdtsc" : "=a" (lo), "=d" (hi));
    _dummy_var_for_mfence.exchange(1); // prevent CPU reorderings
    return (((uint64_t)(hi & ~(1<<31)) << 32) | lo);
}

template<typename... Operations>
struct ActionRecord {
    std::string_view operation_name;
    std::variant<Operations...> operation;

    uint64_t& op_start() {
        return std::visit([] (auto& op) -> uint64_t& {
            return op._op_start;
        }, operation);
    }

    uint64_t& op_end() {
        return std::visit([] (auto& op) -> uint64_t& {
            return op._op_end;
        }, operation);
    }

    MSGPACK_DEFINE_MAP(operation_name, operation);
};

template<typename AnyOperation>
struct logger {};

template<typename ...Operations>
struct logger<std::variant<Operations...>> {
    static logger& instance() {
        static uint64_t init_timestamp = get_timestamp_now();
        static thread_local logger inst{init_timestamp};
        return inst;
    }

    template<typename Operation>
    static Operation& start_operation() {
        auto& current_record = instance().current_record;
        current_record.operation_name = Operation::_name_;
        current_record.operation.template emplace<Operation>();
        current_record.op_start() = get_timestamp_now();
        return ongoing_operation<Operation>();
    }

    template<typename Operation>
    static Operation& ongoing_operation() {
        auto& current_record = instance().current_record;
        return std::get<Operation>(current_record.operation);
    }

    static void mark_operation_start() {
        instance().current_record.op_start() = get_timestamp_now();
    }

    static void mark_operation_end() {
        auto& op_end = instance().current_record.op_end();
        if (op_end == 0) {
            op_end = get_timestamp_now();
        }
    }

    template<typename Operation>
    static void end_operation() {
        auto& current_record = instance().current_record;
        assert(std::holds_alternative<Operation>(current_record.operation));

        mark_operation_end();
        assert(current_record.op_start() <= current_record.op_end());

        auto& log_out = instance().log_out;
        msgpack::pack(log_out, current_record);
        log_out.flush();
    }
private:
    const uint64_t& init_timestamp;
    logger(uint64_t& init_timestamp) :
        init_timestamp{init_timestamp},
        log_out{log_path(), std::ios::binary}
    {}

    const pid_t tid = gettid();
    std::string log_filename() {
        auto& pretty_name = pretty_name_of<std::variant<Operations...>>::value;
        std::ostringstream out;
        out << "tracing-"
            << pretty_name
            << "-"
            << tid
            << ".log";
        auto s = out.str();
        std::cerr << "Writing trace to " << s << std::endl;
        return s;
    }
    std::filesystem::path log_path() {
        const char* dir = std::getenv("OMNILINK_TRACE_DIR");
        if (dir) {
            return std::filesystem::path(dir) / log_filename();
        } else {
            return std::filesystem::current_path() / log_filename();
        }
    }
    std::ofstream log_out;

    ActionRecord<Operations...> current_record;
};

}

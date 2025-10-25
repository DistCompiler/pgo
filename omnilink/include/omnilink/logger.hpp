#pragma once

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <unistd.h>
#include <sys/types.h>
#include <variant>

#include <msgpack.hpp>

namespace omnilink {

static uint64_t get_timestamp_now() {
    unsigned int lo,hi;
    __asm__ __volatile__ ("rdtsc" : "=a" (lo), "=d" (hi));
    return (((uint64_t)(hi & ~(1<<31)) << 32) | lo);
}

static uint64_t init_timestamp = get_timestamp_now();

template<typename AnyOperation>
struct logger {};

template<typename ...Operations>
struct logger<std::variant<Operations...>> {
    static logger& instance() {
        static thread_local logger inst{};
        return inst;
    }

    template<typename Operation>
    static Operation& start_operation() {
        auto& current_record = instance().current_record;
        current_record.op_start = get_timestamp_now();
        current_record.op_end = 0;
        current_record.operation_name = Operation::_name_;
        current_record.operation.template emplace<Operation>();
        current_record.should_succeed = true;
        return ongoing_operation<Operation>();
    }

    template<typename Operation>
    static Operation& ongoing_operation() {
        auto& current_record = instance().current_record;
        return std::get<Operation>(current_record.operation);
    }

    static void mark_operation_start() {
        auto& current_record = instance().current_record;
        current_record.op_start = get_timestamp_now();
    }

    static void mark_operation_end() {
        auto& current_record = instance().current_record;
        if (current_record.op_end == 0) {
            current_record.op_end = get_timestamp_now();
        }
    }

    template<typename Operation>
    static void end_operation() {
        auto& current_record = instance().current_record;
        assert(std::holds_alternative<Operation>(current_record.operation));

        mark_operation_end();
        current_record.should_succeed = !ongoing_operation<Operation>()._did_abort;
        assert(current_record.op_start <= current_record.op_end);

        auto& log_out = instance().log_out;
        msgpack::pack(log_out, current_record);
        log_out.flush();
    }
private:
    const pid_t tid = gettid();
    std::string log_filename() {
        std::ostringstream out;
        out << "tracing-";
        out << tid;
        out << ".log";
        return out.str();
    }
    std::filesystem::path log_path() {
        const char* dir = std::getenv("OMNILINK_TRACE_DIR");
        if (dir) {
            return std::filesystem::path(dir) / log_filename();
        } else {
            return std::filesystem::current_path() / log_filename();
        }
    }
    std::ofstream log_out{log_path(), std::ios::binary};

    struct ActionRecord {
        // Note: TLC can't handle this, but our converter can
        uint64_t op_start, op_end;
        std::string_view operation_name;
        std::variant<Operations...> operation;
        bool should_succeed;
        MSGPACK_DEFINE_MAP(op_start, op_end, operation_name, operation, should_succeed);
    };

    ActionRecord current_record;
};

}

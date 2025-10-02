#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <initializer_list>
#include <iterator>
#include <limits>
#include <msgpack.hpp>
#include <mutex>
#include <optional>
#include <random>
#include <shared_mutex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <wiredtiger.h>
#include "omnilink-lib.hpp"
#include "workload-meta.hpp"

struct NoCopy {
    NoCopy() {}
    NoCopy(const NoCopy&) = delete;
    NoCopy& operator=(const NoCopy&) = delete;
};

static void errorCheck(int ret) {
    if (ret != 0) {
        std::ostringstream out;
        out << "WiredTiger error code " << ret;
        throw std::runtime_error(out.str());
    }
}

struct config {
    std::string str;

    config(std::initializer_list<std::pair<std::string_view, std::string>> pairs) {
        std::ostringstream out;
        bool first = true;
        for(const auto& [name, value] : pairs) {
            out << "," << name << "=" << value;
        }
        str = out.str();
    }

    operator const char*() {
        return str.c_str();
    }
};

std::string hex64(uint64_t ts) {
    std::ostringstream out;
    out << std::hex << ts;
    return out.str();
}

template<typename Self, typename T>
struct HoldsPtr : public NoCopy {
    HoldsPtr() : ptr{nullptr} {}

    HoldsPtr(HoldsPtr<Self, T>&& other) :
        ptr{other.ptr}
    {
        other.ptr = nullptr;
    }

    HoldsPtr<Self, T>& operator=(HoldsPtr<Self, T>&& other) {
        std::swap(ptr, other.ptr);
        return *this;
    }

    T* operator*() {
        return ptr;
    }

    T* operator->() {
        return ptr;
    }

    operator T*() {
        return ptr;
    }

    void setPtr(T* nextPtr) {
        if(ptr) {
            static_cast<Self&>(*this).cleanUp(ptr);
        }
        ptr = nextPtr;
    }

    ~HoldsPtr() {
        setPtr(nullptr);
    }
private:
    T* ptr;
};

struct WtConnection : public HoldsPtr<WtConnection, WT_CONNECTION> {
    WtConnection() {
        auto tmpPath = std::filesystem::current_path() / "tmp";
        WT_CONNECTION* conn;
        errorCheck(wiredtiger_open(tmpPath.c_str(), nullptr, "create=true,log=(enabled=false)", &conn));
        setPtr(conn);
    }

    void cleanUp(WT_CONNECTION* conn) {
        errorCheck(conn->close(conn, nullptr));
    }
};

struct WtSession : public HoldsPtr<WtSession, WT_SESSION> {
    WtSession(WtConnection& conn) {
        WT_SESSION* session;
        errorCheck(conn->open_session(conn, nullptr, "", &session));
        setPtr(session);
        errorCheck(session->create(session, "table:mytable", "key_format=S,value_format=S"));
    }

    void cleanUp(WT_SESSION* session) {
        errorCheck(session->close(session, nullptr));
    }
};

struct WtCursor : public HoldsPtr<WtCursor, WT_CURSOR> {
    WtCursor(WtSession& session) {
        WT_CURSOR* cursor;
        errorCheck(session->open_cursor(session, "table:mytable", nullptr, nullptr, &cursor));
        setPtr(cursor);
    }

    void cleanUp(WT_CURSOR* cursor) {
        errorCheck(cursor->close(cursor));
    }
};

struct WorkloadContext : public omnilink::WorkloadContext<WorkloadContext, Storage::AnyOperation> {
    // SAFETY: always lock in definition order!
    const std::size_t max_kv_count = 20;

    std::shared_mutex existing_kvs_m;
    std::set<uint32_t> existing_kvs;
    
    WtConnection connection;

    std::shared_mutex oldest_timestamp_m;
    uint64_t oldest_timestamp = 0;

    std::shared_mutex stable_timestamp_m;
    uint64_t stable_timestamp = 0;

    std::shared_mutex active_read_timestamps_m;
    std::set<uint64_t> active_read_timestamps;

    struct RunnerDefns : public WorkloadContext::RunnerDefnsBase<RunnerDefns> {
        WtSession session{workload_context.connection};
        WtCursor cursor{session};

        int nextTransactionId = thread_idx;
        int transactionId = -1;
        uint64_t prepare_timestamp = 0;
        bool transactionIsPrepared = false;
        bool transactionHasFailed = false;

        uint64_t find_random_kv() {
            auto read_existing = [&]() -> uint64_t {
                auto idx = std::uniform_int_distribution<std::size_t>{0, workload_context.existing_kvs.size() - 1}(this->rand);
                auto it = workload_context.existing_kvs.begin();
                std::advance(it, idx);
                return *it;
            };

            // First take read lock, only write to the set if you have to.
            auto kv_opt = [&]() -> std::optional<uint64_t> {
                std::shared_lock existing_kvs_lck{workload_context.existing_kvs_m};
                if (workload_context.existing_kvs.size() < workload_context.max_kv_count) {
                    return {};
                } else {
                    return read_existing();
                }
            }();
            if (kv_opt.has_value()) {
                return kv_opt.value();
            } else {
                std::unique_lock existing_kvs_lck{workload_context.existing_kvs_m};
                if (workload_context.existing_kvs.size() < workload_context.max_kv_count) {
                    auto kv = std::uniform_int_distribution{0, std::numeric_limits<int32_t>::max()}(this->rand);
                    workload_context.existing_kvs.insert(kv);
                    return kv;
                } else {
                    return read_existing();
                }
            }
        }

        uint64_t find_timestamp_at(std::initializer_list<uint64_t> constraints) {
            auto lower_bound = std::max(constraints);
            uint64_t upper_bound = std::numeric_limits<int32_t>::max();
            if (lower_bound > upper_bound) {
                throw omnilink::UnsupportedException{};
            }
            return std::uniform_int_distribution<uint64_t>{lower_bound, upper_bound}(this->rand);
        }

        uint64_t max_active_read_timestamp_nolock() {
            auto it = workload_context.active_read_timestamps.rbegin();
            if (it != workload_context.active_read_timestamps.rend()) {
                return *it;
            } else {
                return 0;
            }
        }

        void record_whether_transaction_failed(int ret) {
            if (ret == WT_ROLLBACK) {
                transactionHasFailed = true;
            }
        }

        void void_transaction() {
            transactionId = -1;
            transactionIsPrepared = false;
            transactionHasFailed = false;
        }

        void fill_terminate_meta(omnilink::Packable& meta) {
            // Need to know this info, so we can consider any open
            // transaction aborted on shutdown.
            meta = std::map<std::string, omnilink::Packable>{
                {"transactionId", transactionId},
                {"transactionIsPrepared", transactionIsPrepared},
                {"transactionHasFailed", transactionHasFailed},
            };
        }

        Storage::AbortTransaction perform_operation(omnilink::Tag<Storage::AbortTransaction>) {
            if (transactionId == -1) {
                throw omnilink::UnsupportedException{};
            }
            int ret = session->rollback_transaction(session, nullptr);
            auto rec = Storage::AbortTransaction{
                .n = "n",
                .tid = transactionId,
                ._did_abort = ret != 0,
                ._meta = std::map<std::string, int>{{"result_code", ret}},
            };
            void_transaction();
            return rec;
        }

        Storage::CommitPreparedTransaction perform_operation(omnilink::Tag<Storage::CommitPreparedTransaction>) {
            if (transactionId == -1 || !transactionIsPrepared || transactionHasFailed) {
                throw omnilink::UnsupportedException{};
            }
            int currTransactionId = transactionId;
            std::shared_lock stable_timestamp_lck{workload_context.stable_timestamp_m};
            std::shared_lock active_read_timestamps_lck{workload_context.active_read_timestamps_m};
            auto commit_timestamp = find_timestamp_at({
                this->prepare_timestamp,
                workload_context.stable_timestamp + 1,
                max_active_read_timestamp_nolock(),
            });
            auto durable_timestamp = find_timestamp_at({commit_timestamp});
            int ret = session->commit_transaction(session, config{
                {"commit_timestamp", hex64(commit_timestamp)},
                {"durable_timestamp", hex64(durable_timestamp)},
            });
            // unconditionally void the transaction, either it committed or rolled back
            void_transaction();
            return Storage::CommitPreparedTransaction{
                .n = "n",
                .tid = currTransactionId,
                .commitTs = commit_timestamp,
                .durableTs = durable_timestamp,
                ._did_abort = ret != 0,
                ._meta = std::map<std::string, int>{{"result_code", ret}},
            };
        }

        Storage::CommitTransaction perform_operation(omnilink::Tag<Storage::CommitTransaction>) {
            if (transactionId == -1 || transactionIsPrepared || transactionHasFailed) {
                throw omnilink::UnsupportedException{};
            }
            std::shared_lock stable_timestamp_lck{workload_context.stable_timestamp_m};
            std::shared_lock active_read_timestamps_lck{workload_context.active_read_timestamps_m};
            auto commit_timestamp = find_timestamp_at({
                workload_context.stable_timestamp + 1,
                max_active_read_timestamp_nolock(),
            });
            int currTransactionId = transactionId;
            int ret = session->commit_transaction(session, config{
                {"commit_timestamp", hex64(commit_timestamp)},
            });
            // unconditionally void the transaction, either it committed or rolled back
            void_transaction();
            return Storage::CommitTransaction{
                .n = "n",
                .tid = currTransactionId,
                .commitTs = commit_timestamp,
                ._did_abort = ret != 0,
                ._meta = std::map<std::string, int>{{"result_code", ret}},
            };
        }

        Storage::PrepareTransaction perform_operation(omnilink::Tag<Storage::PrepareTransaction>) {
            if (transactionId == -1 || transactionIsPrepared || transactionHasFailed) {
                throw omnilink::UnsupportedException{};
            }
            std::shared_lock stable_timestamp_lck{workload_context.stable_timestamp_m};
            std::shared_lock active_read_timestamps_lck{workload_context.active_read_timestamps_m};
            auto prepare_timestamp = find_timestamp_at({
                workload_context.stable_timestamp + 1,
                max_active_read_timestamp_nolock(),
            });
            int ret = session->prepare_transaction(session, config{
                {"prepare_timestamp", hex64(prepare_timestamp)},
            });
            if (ret == 0) {
                transactionIsPrepared = true;
                this->prepare_timestamp = prepare_timestamp;
            }
            record_whether_transaction_failed(ret);
            return Storage::PrepareTransaction{
                .n = "n",
                .tid = transactionId,
                .prepareTs = prepare_timestamp,
                ._did_abort = ret != 0,
                ._meta = std::map<std::string, int>{{"result_code", ret}},
            };
        }

        Storage::RollbackToStable perform_operation(omnilink::Tag<Storage::RollbackToStable>) {
            throw omnilink::UnsupportedException{};
        }

        Storage::SetOldestTimestamp perform_operation(omnilink::Tag<Storage::SetOldestTimestamp>) {
            throw omnilink::UnsupportedException{};
        }

        Storage::SetStableTimestamp perform_operation(omnilink::Tag<Storage::SetStableTimestamp>) {
            throw omnilink::UnsupportedException{};
        }

        Storage::StartTransaction perform_operation(omnilink::Tag<Storage::StartTransaction>) {
            if (transactionId != -1) {
                throw omnilink::UnsupportedException{};
            }
            std::shared_lock oldest_timestamp_lck{workload_context.oldest_timestamp_m};
            auto read_timestamp = find_timestamp_at({workload_context.oldest_timestamp});
            {
                std::unique_lock active_read_timestamps_lck{workload_context.active_read_timestamps_m};
                workload_context.active_read_timestamps.insert(read_timestamp);
            }
            int chosenTransactionId;
            int ret = session->begin_transaction(session, config{
                {"read_timestamp", hex64(read_timestamp)}
            });
            if (ret == 0) {
                // Update transaction ID, the transaction has started.
                transactionId = nextTransactionId;
                nextTransactionId += workload_context.thread_count;
                transactionHasFailed = false;
                transactionIsPrepared = false;
                chosenTransactionId = transactionId;
            } else {
                std::unique_lock active_read_timestamps_lck{workload_context.active_read_timestamps_m};
                workload_context.active_read_timestamps.erase(read_timestamp);
                void_transaction();
                chosenTransactionId = -1;
            }
            return Storage::StartTransaction{
                .n = "n",
                .tid = chosenTransactionId,
                .readTs = read_timestamp,
                .rc = "snapshot",
                .ignorePrepare = "false",
                ._did_abort = ret != 0,
                ._meta = std::map<std::string, int>{{"result_code", ret}},
            };
        }

        Storage::TransactionRead perform_operation(omnilink::Tag<Storage::TransactionRead>) {
            // Quirk: ops on a failed transaction may succeed. Avoid that.
            if (transactionId == -1 || transactionIsPrepared || transactionHasFailed) {
                throw omnilink::UnsupportedException{};
            }
            auto key = find_random_kv();
            auto keyStr = std::to_string(key);
            cursor->set_key(cursor, keyStr.c_str());
            int ret = cursor->search(cursor);
            const char* value = "-1";
            if (ret == 0) {
                ret = cursor->get_value(cursor, &value);
            }
            record_whether_transaction_failed(ret);
            return Storage::TransactionRead{
                .n = "n",
                .tid = transactionId,
                .k = key,
                .v = std::atoi(value),
                ._did_abort = ret != 0,
                ._meta = std::map<std::string, int>{{"result_code", ret}},
            };
        }

        Storage::TransactionRemove perform_operation(omnilink::Tag<Storage::TransactionRemove>) {
            // Quirk: ops on a failed transaction may succeed. Avoid that.
            if (transactionId == -1 || transactionIsPrepared || transactionHasFailed) {
                throw omnilink::UnsupportedException{};
            }
            auto key = find_random_kv();
            auto keyStr = std::to_string(key);
            cursor->set_key(cursor, keyStr.c_str());
            int ret = cursor->remove(cursor);
            record_whether_transaction_failed(ret);
            return Storage::TransactionRemove{
                .n = "n",
                .tid = transactionId,
                .k = key,
                ._did_abort = ret != 0,
                ._meta = std::map<std::string, int>{{"result_code", ret}},
            };
        }

        Storage::TransactionWrite perform_operation(omnilink::Tag<Storage::TransactionWrite>) {
            // Quirk: ops on a failed transaction may succeed. Avoid that.
            if (transactionId == -1 || transactionIsPrepared || transactionHasFailed) {
                throw omnilink::UnsupportedException{};
            }
            auto key = find_random_kv();
            auto value = transactionId; // the spec assumes this, let's go with it for now
            auto keyStr = std::to_string(key);
            auto valueStr = std::to_string(transactionId);
            cursor->set_key(cursor, keyStr.c_str());
            cursor->set_value(cursor, valueStr.c_str());
            int ret = cursor->insert(cursor);
            record_whether_transaction_failed(ret);
            return Storage::TransactionWrite{
                .n = "n",
                .tid = transactionId,
                .k = key,
                .v = value,
                .ignoreWriteConflicts = "false",
                ._did_abort = ret != 0,
                ._meta = std::map<std::string, int>{{"result_code", ret}},
            };
        }
    };
};

int main() {
    std::filesystem::create_directory("./tmp");
    return WorkloadContext::main();
}

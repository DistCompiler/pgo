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
#include <omnilink/workload.hpp>
#include <omnilink/models/Storage.hpp>

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
    const std::size_t max_kv_count = 20;
    const std::size_t max_txn_count = 150;
    // SAFETY: always lock in definition order!
    std::shared_mutex connection_m;
    WtConnection connection;

    std::shared_mutex existing_kvs_m;
    std::set<uint32_t> existing_kvs;

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

        uint64_t find_timestamp_at(std::initializer_list<uint64_t> lower_constraints, std::initializer_list<uint64_t> upper_constraints = {std::numeric_limits<int32_t>::max()}) {
            auto lower_bound = std::max(lower_constraints);
            uint64_t upper_bound = std::min(upper_constraints);
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

        void perform_operation(Ctx<Storage::AbortTransaction>& ctx) {
            if (transactionId == -1) ctx.unsupported();
            int ret = session->rollback_transaction(session, nullptr);
            ctx.op.n = "n";
            ctx.op.tid = transactionId;
            ctx.op._did_abort = ret != 0;
            ctx.op._meta = std::map<std::string, int>{{"result_code", ret}};
            void_transaction();
        }

        void perform_operation(Ctx<Storage::CommitPreparedTransaction>& ctx) {
            if (transactionId == -1 || !transactionIsPrepared || transactionHasFailed) {
                ctx.unsupported();
            }
            int currTransactionId = transactionId;
            std::shared_lock connection_lck{workload_context.connection_m};
            std::shared_lock stable_timestamp_lck{workload_context.stable_timestamp_m};
            std::shared_lock active_read_timestamps_lck{workload_context.active_read_timestamps_m};
            auto commit_timestamp = find_timestamp_at({
                this->prepare_timestamp,
                workload_context.stable_timestamp + 1,
                max_active_read_timestamp_nolock(),
            });
            auto durable_timestamp = find_timestamp_at({commit_timestamp});
            ctx.refine_op_start();
            int ret = session->commit_transaction(session, config{
                {"commit_timestamp", hex64(commit_timestamp)},
                {"durable_timestamp", hex64(durable_timestamp)},
            });
            ctx.refine_op_end();
            // unconditionally void the transaction, either it committed or rolled back
            void_transaction();
            ctx.op.n = "n";
            ctx.op.tid = currTransactionId;
            ctx.op.commitTs = commit_timestamp;
            ctx.op.durableTs = durable_timestamp;
            ctx.op._did_abort = ret != 0;
            ctx.op._meta = std::map<std::string, int>{{"result_code", ret}};
        }

        void perform_operation(Ctx<Storage::CommitTransaction>& ctx) {
            if (transactionId == -1 || transactionIsPrepared || transactionHasFailed) {
                ctx.unsupported();
            }
            std::shared_lock connection_lck{workload_context.connection_m};
            std::shared_lock stable_timestamp_lck{workload_context.stable_timestamp_m};
            std::shared_lock active_read_timestamps_lck{workload_context.active_read_timestamps_m};
            auto commit_timestamp = find_timestamp_at({
                workload_context.stable_timestamp + 1,
                max_active_read_timestamp_nolock() + 1,
            });
            int currTransactionId = transactionId;
            ctx.refine_op_start();
            int ret = session->commit_transaction(session, config{
                {"commit_timestamp", hex64(commit_timestamp)},
            });
            ctx.refine_op_end();
            // unconditionally void the transaction, either it committed or rolled back
            void_transaction();
            ctx.op.n = "n";
            ctx.op.tid = currTransactionId;
            ctx.op.commitTs = commit_timestamp;
            ctx.op._did_abort = ret != 0;
            ctx.op._meta = std::map<std::string, int>{{"result_code", ret}};
        }

        void perform_operation(Ctx<Storage::PrepareTransaction>& ctx) {
            if (transactionId == -1 || transactionIsPrepared || transactionHasFailed) {
                ctx.unsupported();
            }
            std::shared_lock connection_lck{workload_context.connection_m};
            std::shared_lock stable_timestamp_lck{workload_context.stable_timestamp_m};
            std::shared_lock active_read_timestamps_lck{workload_context.active_read_timestamps_m};
            auto prepare_timestamp = find_timestamp_at({
                workload_context.stable_timestamp + 1,
                max_active_read_timestamp_nolock() + 1,
            });
            ctx.refine_op_start();
            int ret = session->prepare_transaction(session, config{
                {"prepare_timestamp", hex64(prepare_timestamp)},
            });
            ctx.refine_op_end();
            if (ret == 0) {
                transactionIsPrepared = true;
                this->prepare_timestamp = prepare_timestamp;
            }
            record_whether_transaction_failed(ret);
            ctx.op.n = "n";
            ctx.op.tid = transactionId;
            ctx.op.prepareTs = prepare_timestamp;
            ctx.op._did_abort = ret != 0;
            ctx.op._meta = std::map<std::string, int>{{"result_code", ret}};
        }

        void perform_operation(Ctx<Storage::RollbackToStable>& ctx) {
            std::unique_lock connection_lck{workload_context.connection_m};
            std::unique_lock existing_kvs_lck{workload_context.existing_kvs_m};
            std::unique_lock oldest_timestamp_lck{workload_context.oldest_timestamp_m};
            std::unique_lock stable_timestamp_lck{workload_context.stable_timestamp_m};
            std::unique_lock active_read_timestamps_lck{workload_context.active_read_timestamps_m};
            if(max_active_read_timestamp_nolock() != 0) {
                ctx.unsupported();
            }
            if(workload_context.stable_timestamp == 0) {
                ctx.unsupported();
            }
            ctx.refine_op_start();
            int ret = workload_context.connection->rollback_to_stable(workload_context.connection, nullptr);
            ctx.refine_op_end();
            ctx.op.n = "n";
            ctx.op._did_abort = ret != 0;
            ctx.op._meta = std::map<std::string, int>{{"result_code", ret}};
        }

        void perform_operation(Ctx<Storage::SetOldestTimestamp>& ctx) {
            std::unique_lock connection_lck{workload_context.connection_m};
            std::unique_lock existing_kvs_lck{workload_context.existing_kvs_m};
            std::unique_lock oldest_timestamp_lck{workload_context.oldest_timestamp_m};
            std::unique_lock stable_timestamp_lck{workload_context.stable_timestamp_m};
            uint64_t ts = find_timestamp_at({workload_context.oldest_timestamp}, {workload_context.stable_timestamp});
            // 0 value crashes WT due to assertion
            if (ts == 0) {
                ctx.unsupported();
            }
            ctx.refine_op_start();
            int ret = workload_context.connection->set_timestamp(workload_context.connection, config{{"oldest_timestamp", hex64(ts)}});
            ctx.refine_op_end();
            if (ret == 0) {
                workload_context.oldest_timestamp = ts;
            }
            ctx.op.n = "n";
            ctx.op.ts = ts;
            ctx.op._did_abort = ret != 0;
            ctx.op._meta = std::map<std::string, int>{{"result_code", ret}};
        }

        void perform_operation(Ctx<Storage::SetStableTimestamp>& ctx) {
            std::unique_lock connection_lck{workload_context.connection_m};
            std::unique_lock existing_kvs_lck{workload_context.existing_kvs_m};
            std::unique_lock oldest_timestamp_lck{workload_context.oldest_timestamp_m};
            std::unique_lock stable_timestamp_lck{workload_context.stable_timestamp_m};
            uint64_t ts = find_timestamp_at({workload_context.stable_timestamp});
            ctx.refine_op_start();
            int ret = workload_context.connection->set_timestamp(workload_context.connection, config{{"stable_timestamp", hex64(ts)}});
            ctx.refine_op_end();
            if (ret == 0) {
                workload_context.stable_timestamp = ts;
            }
            ctx.op.n = "n";
            ctx.op.ts = ts;
            ctx.op._did_abort = ret != 0;
            ctx.op._meta = std::map<std::string, int>{{"result_code", ret}};
        }

        void perform_operation(Ctx<Storage::StartTransaction>& ctx) {
            if (transactionId != -1 || nextTransactionId > workload_context.max_txn_count) {
                ctx.unsupported();
            }
            std::shared_lock connection_lck{workload_context.connection_m};
            std::shared_lock oldest_timestamp_lck{workload_context.oldest_timestamp_m};
            auto read_timestamp = find_timestamp_at({workload_context.oldest_timestamp});
            {
                std::unique_lock active_read_timestamps_lck{workload_context.active_read_timestamps_m};
                workload_context.active_read_timestamps.insert(read_timestamp);
            }
            int chosenTransactionId;
            ctx.refine_op_start();
            int ret = session->begin_transaction(session, config{
                {"read_timestamp", hex64(read_timestamp)}
            });
            ctx.refine_op_end();
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
            ctx.op.n = "n";
            ctx.op.tid = chosenTransactionId;
            ctx.op.readTs = read_timestamp;
            ctx.op.rc = "snapshot";
            ctx.op.ignorePrepare = "false";
            ctx.op._did_abort = ret != 0;
            ctx.op._meta = std::map<std::string, int>{{"result_code", ret}};
        }

        void perform_operation(Ctx<Storage::TransactionRead>& ctx) {
            // Quirk: ops on a failed transaction may succeed. Avoid that.
            if (transactionId == -1 || transactionIsPrepared || transactionHasFailed) {
                ctx.unsupported();
            }
            auto key = find_random_kv();
            auto keyStr = std::to_string(key);
            cursor->set_key(cursor, keyStr.c_str());
            ctx.refine_op_start();
            int ret = cursor->search(cursor);
            ctx.refine_op_end();
            const char* value = "-1";
            if (ret == 0) {
                ret = cursor->get_value(cursor, &value);
            }
            record_whether_transaction_failed(ret);
            ctx.op.n = "n";
            ctx.op.tid = transactionId;
            ctx.op.k = key;
            ctx.op.v = std::atoi(value);
            ctx.op._did_abort = ret != 0;
            ctx.op._meta = std::map<std::string, int>{{"result_code", ret}};
        }

        void perform_operation(Ctx<Storage::TransactionRemove>& ctx) {
            // Quirk: ops on a failed transaction may succeed. Avoid that.
            if (transactionId == -1 || transactionIsPrepared || transactionHasFailed) {
                ctx.unsupported();
            }
            auto key = find_random_kv();
            auto keyStr = std::to_string(key);
            cursor->set_key(cursor, keyStr.c_str());
            ctx.refine_op_start();
            int ret = cursor->remove(cursor);
            ctx.refine_op_end();
            record_whether_transaction_failed(ret);
            ctx.op.n = "n";
            ctx.op.tid = transactionId;
            ctx.op.k = key;
            ctx.op._did_abort = ret != 0;
            ctx.op._meta = std::map<std::string, int>{{"result_code", ret}};
        }

        void perform_operation(Ctx<Storage::TransactionWrite>& ctx) {
            // Quirk: ops on a failed transaction may succeed. Avoid that.
            if (transactionId == -1 || transactionIsPrepared || transactionHasFailed) {
                ctx.unsupported();
            }
            auto key = find_random_kv();
            auto value = transactionId; // the spec assumes this, let's go with it for now
            auto keyStr = std::to_string(key);
            auto valueStr = std::to_string(transactionId);
            cursor->set_key(cursor, keyStr.c_str());
            cursor->set_value(cursor, valueStr.c_str());
            ctx.refine_op_start();
            int ret = cursor->insert(cursor);
            ctx.refine_op_end();
            record_whether_transaction_failed(ret);
            ctx.op.n = "n";
            ctx.op.tid = transactionId;
            ctx.op.k = key;
            ctx.op.v = value;
            ctx.op.ignoreWriteConflicts = "false";
            ctx.op._did_abort = ret != 0;
            ctx.op._meta = std::map<std::string, int>{{"result_code", ret}};
        }
    };
};

int main() {
    std::filesystem::create_directory("./tmp");
    return WorkloadContext::main();
}

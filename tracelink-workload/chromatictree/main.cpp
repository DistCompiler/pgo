#include <cstdint>
#include <random>
#include "tracelink-workload.hpp"
#include "workload-meta.hpp"

__thread int tid = 0;
#include "random_xoshiro256pp.h"
//#include "debugprinting.h"

//#include "define_global_statistics.h"
#include "gstats_global.h"

#ifndef DEBUG
#define DEBUG if(0)
#define DEBUG1 if(0)
#define DEBUG2 if(0)
#define DEBUG3 if(0) /* rarely used */
#endif

#include "chromatic.h"
#include "adapter.h"

using DataStructure = ds_adapter<int32_t, int32_t>;

struct auto_init_t {
    DataStructure& ds;
    auto_init_t(int thread_idx, DataStructure& _ds) : ds{_ds} {
        tid = thread_idx;
        ds.initThread(tid);
    }
    ~auto_init_t() {
        ds.deinitThread(tid);
    }
};

struct TreeWorkloadContext: public tracelink::WorkloadContext<TreeWorkloadContext, ChromaticTree::AnyOperation> {
    DataStructure data_structure{
        int(this->thread_count),
        -1,
        -1,
        -1,
        nullptr, // unused (for now)
    };

    struct RunnerDefns: public WorkloadContext::RunnerDefnsBase<RunnerDefns> {
        auto_init_t auto_init{int(this->thread_idx), workload_context.data_structure};

        int32_t rand_kv() {
            return std::uniform_int_distribution<int32_t>(1, 11)(this->rand);
        }

        ChromaticTree::KVInsert perform_operation(tracelink::Tag<ChromaticTree::KVInsert>) {
            int32_t key = rand_kv();
            int32_t value = rand_kv();
            workload_context.data_structure.insert(tid, key, value);
            return ChromaticTree::KVInsert{key, value};
        }

        ChromaticTree::KVInsertIfAbsent perform_operation(tracelink::Tag<ChromaticTree::KVInsertIfAbsent>) {
            int32_t key = rand_kv();
            int32_t value = rand_kv();
            workload_context.data_structure.insert(tid, key, value);
            return ChromaticTree::KVInsertIfAbsent{key, value};
        }

        ChromaticTree::KVContains perform_operation(tracelink::Tag<ChromaticTree::KVContains>) {
            int32_t key = rand_kv();
            bool result = workload_context.data_structure.find(tid, key) != -1;
            return ChromaticTree::KVContains{key, result};
        }

        ChromaticTree::KVErase perform_operation(tracelink::Tag<ChromaticTree::KVErase>) {
            int32_t key = rand_kv();
            workload_context.data_structure.erase(tid, key);
            return ChromaticTree::KVErase{key};
        }

        ChromaticTree::KVRangeQuery perform_operation(tracelink::Tag<ChromaticTree::KVRangeQuery>) {
            int32_t lo = rand_kv();
            int32_t hi = rand_kv();
            if(lo > hi) {
                throw tracelink::UnsupportedException{};
            }
            // nullptr because internal data structure ignores those params entirely
            int count = workload_context.data_structure.rangeQuery(tid, lo, hi, nullptr, nullptr);
            return ChromaticTree::KVRangeQuery{lo, hi, count};
        }
    };
};

int main() {
    TreeWorkloadContext{{
        .operation_count = 20,
        .thread_count = 5,
    }}.run();
    return 0;
}

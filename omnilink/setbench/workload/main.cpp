#include <cstdint>
#include <random>
#include <iostream>
#include <omnilink/workload.hpp>
#include <omnilink/models/SetBench.hpp>

// This is to handle the "wide" case in config, 500 threads
#define MAX_THREADS_POW2 512

thread_local int tid = 0;
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

#include "adapter.h"

using DataStructure = ds_adapter<int32_t, int32_t>;

struct context_init_t {
    DataStructure& ds;
    context_init_t(DataStructure& ds) : ds{ds} {
        tid = 0;
        ds.initThread(0);
    }
    ~context_init_t() {
        // do not deinitThread(0); we need that for reclaiming the data structure
    }
};

struct defns_init_t {
    DataStructure& ds;
    int thread_idx;
    defns_init_t(int thread_idx, DataStructure& ds) : ds{ds} {
        this->thread_idx = thread_idx;
        tid = thread_idx;
        ds.initThread(thread_idx);
    }
    ~defns_init_t() {
        //ds.deinitThread(thread_idx);
        //std::cout << "called deinitThread with " << thread_idx << std::endl;
    }
};

struct TreeWorkloadContext: public omnilink::WorkloadContext<TreeWorkloadContext, SetBench::AnyOperation> {
    DataStructure data_structure{
        int(this->thread_count + 1), // +1 because this constructor (main thread) counts!
        12, // max key
        -1, // ignored
        0, // it's a bitwise nullptr
        nullptr, // unused (for now)
    };
    context_init_t init{data_structure};

    struct RunnerDefns: public WorkloadContext::RunnerDefnsBase<RunnerDefns> {
        defns_init_t init{int(this->thread_idx), workload_context.data_structure};

        int32_t rand_kv() {
            return std::uniform_int_distribution<int32_t>(1, 11)(this->rand);
        }

        void perform_operation(Ctx<SetBench::KVInsert>& ctx) {
            assert(tid == thread_idx);
            int32_t key = rand_kv();
            int32_t value = rand_kv();
            int32_t result = workload_context.data_structure.insert(thread_idx, key, value);
            ctx.op.key = key;
            ctx.op.value = value;
            ctx.op.result = result;
        }

        void perform_operation(Ctx<SetBench::KVInsertIfAbsent>& ctx) {
            assert(tid == thread_idx);
            int32_t key = rand_kv();
            int32_t value = rand_kv();
            int32_t result = workload_context.data_structure.insertIfAbsent(thread_idx, key, value);
            ctx.op.key = key;
            ctx.op.value = value;
            ctx.op.result = result;
        }

        void perform_operation(Ctx<SetBench::KVContains>& ctx) {
            assert(tid == thread_idx);
            int32_t key = rand_kv();
            bool result = workload_context.data_structure.contains(thread_idx, key);
            ctx.op.key = key;
            ctx.op.result = result;
        }

        void perform_operation(Ctx<SetBench::KVErase>& ctx) {
            assert(tid == thread_idx);
            int32_t key = rand_kv();
            int32_t result = workload_context.data_structure.erase(thread_idx, key);
            ctx.op.key = key;
            ctx.op.result = result;
        }

        void perform_operation(Ctx<SetBench::KVRangeQuery>& ctx) {
            assert(tid == thread_idx);
            int32_t lo = rand_kv();
            int32_t hi = rand_kv();
            if(lo > hi) {
                throw omnilink::UnsupportedException{};
            }
            // nullptr because internal data structure ignores those params entirely
            int count = workload_context.data_structure.rangeQuery(thread_idx, lo, hi, nullptr, nullptr);
            ctx.op.lo = lo;
            ctx.op.hi = hi;
            ctx.op.count = count;
        }
    };
};

int main() {
    return TreeWorkloadContext::main();
}

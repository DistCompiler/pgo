#include <iostream>
#include <msgpack.hpp>
#include "tracelink-workload.hpp"
#include "Storage.hpp"

struct WorkloadContext : public tracelink::WorkloadContext<WorkloadContext, Storage::AnyOperation> {
    struct RunnerDefns : public WorkloadContext::RunnerDefnsBase<RunnerDefns> {
        TRACELINK_RUNNER_DEFNS_INIT(RunnerDefns)

        Storage::AbortTransaction perform_operation(tracelink::Tag<Storage::AbortTransaction>) {
            return Storage::AbortTransaction{};
        }

        Storage::CommitPreparedTransaction perform_operation(tracelink::Tag<Storage::CommitPreparedTransaction>) {
            return Storage::CommitPreparedTransaction{};
        }

        Storage::CommitTransaction perform_operation(tracelink::Tag<Storage::CommitTransaction>) {
            return Storage::CommitTransaction{};
        }

        Storage::PrepareTransaction perform_operation(tracelink::Tag<Storage::PrepareTransaction>) {
            return Storage::PrepareTransaction{};
        }

        Storage::RollbackToStable perform_operation(tracelink::Tag<Storage::RollbackToStable>) {
            return Storage::RollbackToStable{};
        }

        Storage::SetOldestTimestamp perform_operation(tracelink::Tag<Storage::SetOldestTimestamp>) {
            return Storage::SetOldestTimestamp{};
        }

        Storage::SetStableTimestamp perform_operation(tracelink::Tag<Storage::SetStableTimestamp>) {
            return Storage::SetStableTimestamp{};
        }

        Storage::StartTransaction perform_operation(tracelink::Tag<Storage::StartTransaction>) {
            return Storage::StartTransaction{};
        }

        Storage::TransactionRead perform_operation(tracelink::Tag<Storage::TransactionRead>) {
            return Storage::TransactionRead{};
        }

        Storage::TransactionRemove perform_operation(tracelink::Tag<Storage::TransactionRemove>) {
            return Storage::TransactionRemove{};
        }

        Storage::TransactionWrite perform_operation(tracelink::Tag<Storage::TransactionWrite>) {
            return Storage::TransactionWrite{};
        }
    };
};

int main() {
    WorkloadContext{}.run();
    return 0;
}

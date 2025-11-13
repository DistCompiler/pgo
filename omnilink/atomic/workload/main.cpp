#include <cstdint>
#include <atomic>
#include <omnilink/workload.hpp>
#include <omnilink/models/Atomic.hpp>

struct AtomicWorkloadContext: public omnilink::WorkloadContext<AtomicWorkloadContext, Atomic::AnyOperation> {
    std::atomic<int32_t> x{1};

    struct RunnerDefns: public WorkloadContext::RunnerDefnsBase<RunnerDefns> {
        void perform_operation(Ctx<Atomic::Inc>& ctx) {
            ctx.op.prev_x = workload_context.x.fetch_add(1, std::memory_order_acq_rel);
        }
    };
};

int main() {
    return AtomicWorkloadContext::main();
}

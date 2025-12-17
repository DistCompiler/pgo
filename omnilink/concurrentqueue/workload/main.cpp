#line 2 CONCURRENTQUEUE_ORIG_SRC_FILE
#include <concurrentqueue/moodycamel/concurrentqueue.h>
#include <cstdint>
#include <limits>
#include <omnilink/models/ConcurrentQueue.hpp>
#include <omnilink/workload.hpp>
#include <random>
#include <span>

struct QueueWorkloadContext
    : public omnilink::WorkloadContext<QueueWorkloadContext,
                                       ConcurrentQueue::AnyOperation> {
  static constexpr size_t size_limit = 16;
  // Config with deliberately small numbers to help reach edge cases within
  // model checking limits.
  struct CQTraits : public moodycamel::ConcurrentQueueDefaultTraits {
    static const size_t BLOCK_SIZE = 4;
    static const size_t INITIAL_IMPLICIT_PRODUCER_HASH_SIZE = 8;
  };
  moodycamel::ConcurrentQueue<int32_t, CQTraits> queue{};

  std::atomic<size_t> total_elems{0};

  struct RunnerDefns : public WorkloadContext::RunnerDefnsBase<RunnerDefns> {
    static constexpr size_t max_bulk_size = 10;
    int32_t rand_bulk_size() {
      return std::uniform_int_distribution<int32_t>(0,
                                                    max_bulk_size)(this->rand);
    }
    int32_t rand_element() {
      // Here we ensure elements enqueued by a given thread are never equal to
      // another's Not necessary strictly, but it makes validation less
      // ambiguous
      size_t thread_num = thread_idx + 1;
      return std::uniform_int_distribution<int32_t>(
          thread_num * 10, (thread_num + 1) * 10 - 1)(this->rand);
    }

    // TODO: consider adding tokens back

    // thread-local persistent bulk array
    int32_t elems[max_bulk_size] = {-1};
    moodycamel::ProducerToken producer_token{workload_context.queue};

    void perform_operation(Ctx<ConcurrentQueue::Dequeue> &ctx) {
      for (int32_t &elem : elems) {
        elem = -1;
      }
      size_t size = rand_bulk_size();
      size_t actual_size = workload_context.queue.try_dequeue_bulk(elems, size);
      ctx.op.elements = std::span(elems).subspan(0, actual_size);
      ctx.op.consumer = thread_idx;
      workload_context.total_elems -= actual_size;
    }

    void perform_operation(Ctx<ConcurrentQueue::EnqueueWithToken> &ctx) {
      size_t size = rand_bulk_size();
      // Set total_elems optimistically, and decrement it only if things go
      // badly.
      size_t total_elems_seen =
          workload_context.total_elems.fetch_add(size) + size;
      // Don't overinflate the queue, it just makes TLC really slow.
      if (total_elems_seen > size_limit) {
        workload_context.total_elems -= size;
        ctx.unsupported();
      }
      for (int32_t &elem : elems) {
        elem = -1;
      }
      for (size_t i = 0; i < size; ++i) {
        elems[i] = rand_element();
      }
      bool success =
          workload_context.queue.enqueue_bulk(producer_token, elems, size);
      ctx.op.producer = thread_idx;
      ctx.op.elements = std::span(elems).subspan(0, size);
      ctx.op._did_abort = !success;
      if (!success) {
        workload_context.total_elems -= size;
      }
    }

    void perform_operation(Ctx<ConcurrentQueue::DequeueWithToken> &ctx) {
      // ctx.unsupported();
      for (int32_t &elem : elems) {
        elem = -1;
      }
      size_t size = rand_bulk_size();
      size_t actual_size =
          workload_context.queue.try_dequeue_bulk_from_producer(producer_token,
                                                                elems, size);
      ctx.op.producer = thread_idx;
      ctx.op.elements = std::span(elems).subspan(0, actual_size);
      workload_context.total_elems -= actual_size;
    }

    void perform_operation(Ctx<ConcurrentQueue::SizeApprox> &ctx) {
      size_t result = workload_context.queue.size_approx();
      assert(result <= std::numeric_limits<int32_t>::max());
      ctx.op.size = result;
    }
  };
};

int main() { return QueueWorkloadContext::main(); }

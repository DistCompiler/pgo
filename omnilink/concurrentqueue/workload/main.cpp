#include <cstdint>
#include <random>
#include <memory>
#include <vector>
#include <omnilink/workload.hpp>
#include <omnilink/models/ConcurrentQueueAPI.hpp>
#include <concurrentqueue/moodycamel/concurrentqueue.h>

struct QueueWorkloadContext: public omnilink::WorkloadContext<QueueWorkloadContext, ConcurrentQueueAPI::AnyOperation> {
    moodycamel::ConcurrentQueue<int32_t> queue{};

    struct RunnerDefns: public WorkloadContext::RunnerDefnsBase<RunnerDefns> {
        int32_t rand_element() { 
            return std::uniform_int_distribution<int32_t>(1, 100)(this->rand); 
        }
        
        int32_t rand_bulk_size() { 
            return std::uniform_int_distribution<int32_t>(1, 5)(this->rand); 
        }

        std::unique_ptr<moodycamel::ProducerToken> create_producer_token() {
            return std::make_unique<moodycamel::ProducerToken>(workload_context.queue);
        }

        std::unique_ptr<moodycamel::ConsumerToken> create_consumer_token() {
            return std::make_unique<moodycamel::ConsumerToken>(workload_context.queue);
        }

        void perform_operation(Ctx<ConcurrentQueueAPI::QueueEnqueue>& ctx) {
            int32_t element = rand_element();
            bool success = workload_context.queue.enqueue(element);
            ctx.op = ConcurrentQueueAPI::QueueEnqueue{element, success};
            ctx.op.thread = static_cast<int32_t>(thread_idx);
        }

        // void perform_operation(Ctx<ConcurrentQueueAPI::QueueEnqueueWithToken>& ctx) {
        //     int32_t element = rand_element();
        //     auto token = create_producer_token();
        //     bool success = workload_context.queue.enqueue(*token, element);
        //     ctx.op = ConcurrentQueueAPI::QueueEnqueueWithToken{static_cast<int32_t>(thread_idx), element, success};
        //     ctx.op._meta = std::map<std::string, omnilink::Packable>{
        //         {"token_created", true},
        //         {"token_type", "producer"},
        //         {"thread_id", static_cast<int32_t>(thread_idx)}
        //     };
        // }

        // void perform_operation(Ctx<ConcurrentQueueAPI::QueueEnqueueBulk>& ctx) {
        //     int32_t count = rand_bulk_size();
        //     std::vector<int32_t> elements(count);
        //     for (int32_t i = 0; i < count; i++) {
        //         elements[i] = rand_element();
        //     }
        //     bool success = workload_context.queue.enqueue_bulk(elements.data(), count);
        //     ctx.op = ConcurrentQueueAPI::QueueEnqueueBulk{elements, count, success};
        // }

        // void perform_operation(Ctx<ConcurrentQueueAPI::QueueEnqueueBulkWithToken>& ctx) {
        //     int32_t count = rand_bulk_size();
        //     std::vector<int32_t> elements(count);
        //     for (int32_t i = 0; i < count; i++) {
        //         elements[i] = rand_element();
        //     }
        //     auto token = create_producer_token();
        //     size_t enqueued = workload_context.queue.enqueue_bulk(*token, elements.data(), count);
        //     ctx.op = ConcurrentQueueAPI::QueueEnqueueBulkWithToken{static_cast<int32_t>(thread_idx), elements, count, enqueued == static_cast<size_t>(count)};
        //     ctx.op._meta = std::map<std::string, omnilink::Packable>{
        //         {"token_created", true},
        //         {"token_type", "producer"},
        //         {"thread_id", static_cast<int32_t>(thread_idx)}
        //     };
        // }

        void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryEnqueue>& ctx) {
            int32_t element = rand_element();
            bool success = workload_context.queue.try_enqueue(element);
            ctx.op = ConcurrentQueueAPI::QueueTryEnqueue{element, success};
            ctx.op.thread = static_cast<int32_t>(thread_idx);
        }

        // void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryEnqueueWithToken>& ctx) {
        //     int32_t element = rand_element();
        //     auto token = create_producer_token();
        //     bool success = workload_context.queue.try_enqueue(*token, element);
        //     ctx.op = ConcurrentQueueAPI::QueueTryEnqueueWithToken{static_cast<int32_t>(thread_idx), element, success};
        //     ctx.op._meta = std::map<std::string, omnilink::Packable>{
        //         {"token_created", true},
        //         {"token_type", "producer"},
        //         {"thread_id", static_cast<int32_t>(thread_idx)}
        //     };
        // }

        // void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryEnqueueBulk>& ctx) {
        //     int32_t count = rand_bulk_size();
        //     std::vector<int32_t> elements(count);
        //     for (int32_t i = 0; i < count; i++) {
        //         elements[i] = rand_element();
        //     }
        //     bool success = workload_context.queue.try_enqueue_bulk(elements.data(), count);
        //     ctx.op = ConcurrentQueueAPI::QueueTryEnqueueBulk{elements, count, success};
        // }

        // void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryEnqueueBulkWithToken>& ctx) {
        //     int32_t count = rand_bulk_size();
        //     std::vector<int32_t> elements(count);
        //     for (int32_t i = 0; i < count; i++) {
        //         elements[i] = rand_element();
        //     }
        //     auto token = create_producer_token();
        //     size_t enqueued = workload_context.queue.try_enqueue_bulk(*token, elements.data(), count);
        //     ctx.op = ConcurrentQueueAPI::QueueTryEnqueueBulkWithToken{static_cast<int32_t>(thread_idx), elements, count, enqueued == static_cast<size_t>(count)};
        //     ctx.op._meta = std::map<std::string, omnilink::Packable>{
        //         {"token_created", true},
        //         {"token_type", "producer"},
        //         {"thread_id", static_cast<int32_t>(thread_idx)}
        //     };
        // }

        void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryDequeue>& ctx) {
            int32_t element = 0;
            bool success = workload_context.queue.try_dequeue(element);
            ctx.op = ConcurrentQueueAPI::QueueTryDequeue{element, success};
            ctx.op.thread = static_cast<int32_t>(thread_idx);
        }

        // void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryDequeueWithToken>& ctx) {
        //     int32_t element = 0;
        //     auto token = create_consumer_token();
        //     bool success = workload_context.queue.try_dequeue(*token, element);
        //     ctx.op = ConcurrentQueueAPI::QueueTryDequeueWithToken{static_cast<int32_t>(thread_idx), element, success};
        //     ctx.op._meta = std::map<std::string, omnilink::Packable>{
        //         {"token_created", true},
        //         {"token_type", "consumer"},
        //         {"thread_id", static_cast<int32_t>(thread_idx)}
        //     };
        // }

        // void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryDequeueBulk>& ctx) {
        //     int32_t max = rand_bulk_size();
        //     std::vector<int32_t> elements(max);
        //     size_t dequeued = workload_context.queue.try_dequeue_bulk(elements.data(), max);
        //     elements.resize(dequeued);
        //     ctx.op = ConcurrentQueueAPI::QueueTryDequeueBulk{elements, max, static_cast<int32_t>(dequeued)};
        // }

        // void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryDequeueBulkWithToken>& ctx) {
        //     int32_t max = rand_bulk_size();
        //     std::vector<int32_t> elements(max);
        //     auto token = create_consumer_token();
        //     size_t dequeued = workload_context.queue.try_dequeue_bulk(*token, elements.data(), max);
        //     elements.resize(dequeued);
        //     ctx.op = ConcurrentQueueAPI::QueueTryDequeueBulkWithToken{static_cast<int32_t>(thread_idx), elements, max, static_cast<int32_t>(dequeued)};
        //     ctx.op._meta = std::map<std::string, omnilink::Packable>{
        //         {"token_created", true},
        //         {"token_type", "consumer"},
        //         {"thread_id", static_cast<int32_t>(thread_idx)}
        //     };
        // }

        // void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryDequeueFromProducer>& ctx) {
        //     int32_t element = 0;
        //     auto token = create_producer_token();
        //     bool success = workload_context.queue.try_dequeue_from_producer(*token, element);
        //     ctx.op = ConcurrentQueueAPI::QueueTryDequeueFromProducer{static_cast<int32_t>(thread_idx), element, success};
        //     ctx.op._meta = std::map<std::string, omnilink::Packable>{
        //         {"token_created", true},
        //         {"token_type", "producer"},
        //         {"thread_id", static_cast<int32_t>(thread_idx)}
        //     };
        // }

        // void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryDequeueBulkFromProducer>& ctx) {
        //     int32_t max = rand_bulk_size();
        //     std::vector<int32_t> elements(max);
        //     auto token = create_producer_token();
        //     size_t dequeued = workload_context.queue.try_dequeue_bulk_from_producer(*token, elements.data(), max);
        //     elements.resize(dequeued);
        //     ctx.op = ConcurrentQueueAPI::QueueTryDequeueBulkFromProducer{static_cast<int32_t>(thread_idx), elements, max, static_cast<int32_t>(dequeued)};
        //     ctx.op._meta = std::map<std::string, omnilink::Packable>{
        //         {"token_created", true},
        //         {"token_type", "producer"},
        //         {"thread_id", static_cast<int32_t>(thread_idx)}
        //     };
        // }

        void perform_operation(Ctx<ConcurrentQueueAPI::QueueSizeApprox>& ctx) {
            ctx.op = ConcurrentQueueAPI::QueueSizeApprox{static_cast<int32_t>(workload_context.queue.size_approx())};
            ctx.op.thread = static_cast<int32_t>(thread_idx);
        }
    };
};

int main() {
    return QueueWorkloadContext::main();
}

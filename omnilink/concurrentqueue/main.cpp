#include <cstdint>
#include <random>
#include <memory>
#include <vector>
#include "omnilink-lib.hpp"
#include "workload-meta.hpp"
#include "concurrentqueue.h"

struct QueueWorkloadContext: public omnilink::WorkloadContext<QueueWorkloadContext, ConcurrentQueueAPI::AnyOperation> {
    moodycamel::ConcurrentQueue<int32_t> queue;
    std::vector<std::unique_ptr<moodycamel::ProducerToken>> producer_tokens;
    std::vector<std::unique_ptr<moodycamel::ConsumerToken>> consumer_tokens;
    
    QueueWorkloadContext() {
        producer_tokens.resize(thread_count + 1);
        consumer_tokens.resize(thread_count + 1);
        producer_tokens[0] = std::make_unique<moodycamel::ProducerToken>(queue);
        consumer_tokens[0] = std::make_unique<moodycamel::ConsumerToken>(queue);
    }

    struct RunnerDefns: public WorkloadContext::RunnerDefnsBase<RunnerDefns> {
        struct ThreadInit {
            ThreadInit(QueueWorkloadContext& ctx, std::size_t tid) {
                if (tid < ctx.producer_tokens.size()) {
                    ctx.producer_tokens[tid] = std::make_unique<moodycamel::ProducerToken>(ctx.queue);
                    ctx.consumer_tokens[tid] = std::make_unique<moodycamel::ConsumerToken>(ctx.queue);
                }
            }
        } thread_init{workload_context, thread_idx};

        int32_t rand_element() { 
            return std::uniform_int_distribution<int32_t>(1, 100)(this->rand); 
        }
        
        int32_t rand_bulk_size() { 
            return std::uniform_int_distribution<int32_t>(1, 5)(this->rand); 
        }

        ConcurrentQueueAPI::QueueEnqueue perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueEnqueue>) {
            int32_t element = rand_element();
            bool success = workload_context.queue.enqueue(element);
            return ConcurrentQueueAPI::QueueEnqueue{element, success};
        }

        ConcurrentQueueAPI::QueueEnqueueWithToken perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueEnqueueWithToken>) {
            int32_t element = rand_element();
            bool success = false;
            if (thread_idx < workload_context.producer_tokens.size() && workload_context.producer_tokens[thread_idx]) {
                success = workload_context.queue.enqueue(*workload_context.producer_tokens[thread_idx], element);
            }
            return ConcurrentQueueAPI::QueueEnqueueWithToken{thread_idx, element, success};
        }

        ConcurrentQueueAPI::QueueEnqueueBulk perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueEnqueueBulk>) {
            int32_t count = rand_bulk_size();
            std::vector<int32_t> elements(count);
            for (int32_t i = 0; i < count; i++) {
                elements[i] = rand_element();
            }
            size_t enqueued = workload_context.queue.enqueue_bulk(elements.data(), count);
            return ConcurrentQueueAPI::QueueEnqueueBulk{elements, count, enqueued == static_cast<size_t>(count)};
        }

        ConcurrentQueueAPI::QueueEnqueueBulkWithToken perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueEnqueueBulkWithToken>) {
            int32_t count = rand_bulk_size();
            std::vector<int32_t> elements(count);
            for (int32_t i = 0; i < count; i++) {
                elements[i] = rand_element();
            }
            size_t enqueued = 0;
            if (thread_idx < workload_context.producer_tokens.size() && workload_context.producer_tokens[thread_idx]) {
                enqueued = workload_context.queue.enqueue_bulk(*workload_context.producer_tokens[thread_idx], elements.data(), count);
            }
            return ConcurrentQueueAPI::QueueEnqueueBulkWithToken{thread_idx, elements, count, enqueued == static_cast<size_t>(count)};
        }

        ConcurrentQueueAPI::QueueTryEnqueue perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueTryEnqueue>) {
            int32_t element = rand_element();
            bool success = workload_context.queue.try_enqueue(element);
            return ConcurrentQueueAPI::QueueTryEnqueue{element, success};
        }

        ConcurrentQueueAPI::QueueTryEnqueueWithToken perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueTryEnqueueWithToken>) {
            int32_t element = rand_element();
            bool success = false;
            if (thread_idx < workload_context.producer_tokens.size() && workload_context.producer_tokens[thread_idx]) {
                success = workload_context.queue.try_enqueue(*workload_context.producer_tokens[thread_idx], element);
            }
            return ConcurrentQueueAPI::QueueTryEnqueueWithToken{thread_idx, element, success};
        }

        ConcurrentQueueAPI::QueueTryEnqueueBulk perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueTryEnqueueBulk>) {
            int32_t count = rand_bulk_size();
            std::vector<int32_t> elements(count);
            for (int32_t i = 0; i < count; i++) {
                elements[i] = rand_element();
            }
            size_t enqueued = workload_context.queue.try_enqueue_bulk(elements.data(), count);
            return ConcurrentQueueAPI::QueueTryEnqueueBulk{elements, count, enqueued == static_cast<size_t>(count)};
        }

        ConcurrentQueueAPI::QueueTryEnqueueBulkWithToken perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueTryEnqueueBulkWithToken>) {
            int32_t count = rand_bulk_size();
            std::vector<int32_t> elements(count);
            for (int32_t i = 0; i < count; i++) {
                elements[i] = rand_element();
            }
            size_t enqueued = 0;
            if (thread_idx < workload_context.producer_tokens.size() && workload_context.producer_tokens[thread_idx]) {
                enqueued = workload_context.queue.try_enqueue_bulk(*workload_context.producer_tokens[thread_idx], elements.data(), count);
            }
            return ConcurrentQueueAPI::QueueTryEnqueueBulkWithToken{thread_idx, elements, count, enqueued == static_cast<size_t>(count)};
        }

        ConcurrentQueueAPI::QueueTryDequeue perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueTryDequeue>) {
            int32_t element = 0;
            bool success = workload_context.queue.try_dequeue(element);
            return ConcurrentQueueAPI::QueueTryDequeue{element, success};
        }

        ConcurrentQueueAPI::QueueTryDequeueWithToken perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueTryDequeueWithToken>) {
            int32_t element = 0;
            bool success = false;
            if (thread_idx < workload_context.consumer_tokens.size() && workload_context.consumer_tokens[thread_idx]) {
                success = workload_context.queue.try_dequeue(*workload_context.consumer_tokens[thread_idx], element);
            }
            return ConcurrentQueueAPI::QueueTryDequeueWithToken{thread_idx, element, success};
        }

        ConcurrentQueueAPI::QueueTryDequeueBulk perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueTryDequeueBulk>) {
            int32_t max = rand_bulk_size();
            std::vector<int32_t> elements(max);
            size_t dequeued = workload_context.queue.try_dequeue_bulk(elements.data(), max);
            elements.resize(dequeued);
            return ConcurrentQueueAPI::QueueTryDequeueBulk{elements, max, static_cast<int32_t>(dequeued)};
        }

        ConcurrentQueueAPI::QueueTryDequeueBulkWithToken perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueTryDequeueBulkWithToken>) {
            int32_t max = rand_bulk_size();
            std::vector<int32_t> elements(max);
            size_t dequeued = 0;
            if (thread_idx < workload_context.consumer_tokens.size() && workload_context.consumer_tokens[thread_idx]) {
                dequeued = workload_context.queue.try_dequeue_bulk(*workload_context.consumer_tokens[thread_idx], elements.data(), max);
            }
            elements.resize(dequeued);
            return ConcurrentQueueAPI::QueueTryDequeueBulkWithToken{thread_idx, elements, max, static_cast<int32_t>(dequeued)};
        }

        ConcurrentQueueAPI::QueueTryDequeueFromProducer perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueTryDequeueFromProducer>) {
            int32_t element = 0;
            bool success = false;
            if (thread_idx < workload_context.producer_tokens.size() && workload_context.producer_tokens[thread_idx]) {
                success = workload_context.queue.try_dequeue_from_producer(*workload_context.producer_tokens[thread_idx], element);
            }
            return ConcurrentQueueAPI::QueueTryDequeueFromProducer{thread_idx, element, success};
        }

        ConcurrentQueueAPI::QueueTryDequeueBulkFromProducer perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueTryDequeueBulkFromProducer>) {
            int32_t max = rand_bulk_size();
            std::vector<int32_t> elements(max);
            size_t dequeued = 0;
            if (thread_idx < workload_context.producer_tokens.size() && workload_context.producer_tokens[thread_idx]) {
                dequeued = workload_context.queue.try_dequeue_bulk_from_producer(*workload_context.producer_tokens[thread_idx], elements.data(), max);
            }
            elements.resize(dequeued);
            return ConcurrentQueueAPI::QueueTryDequeueBulkFromProducer{thread_idx, elements, max, static_cast<int32_t>(dequeued)};
        }

        ConcurrentQueueAPI::QueueSizeApprox perform_operation(omnilink::Tag<ConcurrentQueueAPI::QueueSizeApprox>) {
            return ConcurrentQueueAPI::QueueSizeApprox{static_cast<int32_t>(workload_context.queue.size_approx())};
        }

        ConcurrentQueueAPI::CreateProducerToken perform_operation(omnilink::Tag<ConcurrentQueueAPI::CreateProducerToken>) {
            return ConcurrentQueueAPI::CreateProducerToken{thread_idx};
        }

        ConcurrentQueueAPI::CreateConsumerToken perform_operation(omnilink::Tag<ConcurrentQueueAPI::CreateConsumerToken>) {
            return ConcurrentQueueAPI::CreateConsumerToken{thread_idx};
        }
    };
};

int main() {
    return QueueWorkloadContext::main();
}

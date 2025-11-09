#include <atomic>
#include <cstdint>
#include <deque>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <random>
#include <unordered_map>
#include <vector>
#include <omnilink/workload.hpp>
#include <omnilink/models/ConcurrentQueueAPI.hpp>
#include <concurrentqueue/moodycamel/concurrentqueue.h>

struct QueueWorkloadContext: public omnilink::WorkloadContext<QueueWorkloadContext, ConcurrentQueueAPI::AnyOperation> {
    moodycamel::ConcurrentQueue<int32_t> queue{};
    std::atomic<int32_t> next_element_id{1};
    std::mutex instrumentation_mutex;
    std::unordered_map<int32_t, std::deque<int32_t>> pending_per_thread;

    int32_t next_element() {
        return next_element_id.fetch_add(1, std::memory_order_relaxed);
    }

    void record_enqueue(size_t thread_idx, int32_t element) {
        std::lock_guard<std::mutex> lock(instrumentation_mutex);
        auto &pending = pending_per_thread[static_cast<int32_t>(thread_idx)];
        pending.push_back(element);
    }

    std::optional<int32_t> resolve_producer_for_dequeue(int32_t element) {
        std::lock_guard<std::mutex> lock(instrumentation_mutex);
        for (auto it = pending_per_thread.begin(); it != pending_per_thread.end(); ++it) {
            auto &pending = it->second;
            if (!pending.empty() && pending.front() == element) {
                pending.pop_front();
                int32_t producer = it->first;
                if (pending.empty()) {
                    pending_per_thread.erase(it);
                }
                return producer;
            }
        }
        return std::nullopt;
    }

    std::optional<std::vector<int32_t>> resolve_producers_for_bulk(const int32_t* elements, size_t count) {
        if (count == 0) {
            return std::nullopt;
        }

        std::lock_guard<std::mutex> lock(instrumentation_mutex);

        std::vector<int32_t> producers;
        producers.reserve(count);

        for (size_t idx = 0; idx < count; ++idx) {
            auto found = pending_per_thread.end();
            for (auto it = pending_per_thread.begin(); it != pending_per_thread.end(); ++it) {
                auto &pending = it->second;
                if (!pending.empty() && pending.front() == elements[idx]) {
                    found = it;
                    break;
                }
            }

            if (found == pending_per_thread.end()) {
                return std::nullopt;
            }

            producers.push_back(found->first);
            auto &pending = found->second;
            pending.pop_front();
            if (pending.empty()) {
                pending_per_thread.erase(found);
            }
        }

        return producers;
    }

    struct RunnerDefns: public WorkloadContext::RunnerDefnsBase<RunnerDefns> {
        int32_t next_element() {
            return workload_context.next_element();
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
            int32_t element = next_element();
            bool success = workload_context.queue.enqueue(element);
            ctx.op = ConcurrentQueueAPI::QueueEnqueue{element, success};
            ctx.op.thread = static_cast<int32_t>(thread_idx);
            if (success) {
                workload_context.record_enqueue(thread_idx, element);
            }
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

        void perform_operation(Ctx<ConcurrentQueueAPI::QueueEnqueueBulk>& ctx) {
            int32_t count = rand_bulk_size();
            std::vector<int32_t> elements(count);
            for (int32_t i = 0; i < count; i++) {
                elements[i] = next_element();
            }
            bool success = workload_context.queue.enqueue_bulk(elements.data(), count);
            ctx.op = ConcurrentQueueAPI::QueueEnqueueBulk{elements, count, success};
            ctx.op.thread = static_cast<int32_t>(thread_idx);
            if (success) {
                for (auto element : elements) {
                    workload_context.record_enqueue(thread_idx, element);
                }
            }
        }

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
            int32_t element = next_element();
            bool success = workload_context.queue.try_enqueue(element);
            ctx.op = ConcurrentQueueAPI::QueueTryEnqueue{element, success};
            ctx.op.thread = static_cast<int32_t>(thread_idx);
            if (success) {
                workload_context.record_enqueue(thread_idx, element);
            }
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

        void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryEnqueueBulk>& ctx) {
            int32_t count = rand_bulk_size();
            std::vector<int32_t> elements(count);
            for (int32_t i = 0; i < count; i++) {
                elements[i] = next_element();
            }
            bool success = workload_context.queue.try_enqueue_bulk(elements.data(), count);
            ctx.op = ConcurrentQueueAPI::QueueTryEnqueueBulk{elements, count, success};
            ctx.op.thread = static_cast<int32_t>(thread_idx);
            if (success) {
                for (auto element : elements) {
                    workload_context.record_enqueue(thread_idx, element);
                }
            }
        }

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

            int32_t producer_thread = static_cast<int32_t>(thread_idx);
            if (success) {
                if (auto resolved = workload_context.resolve_producer_for_dequeue(element)) {
                    producer_thread = *resolved;
                }
            }

            ctx.op.thread = producer_thread;
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

        void perform_operation(Ctx<ConcurrentQueueAPI::QueueTryDequeueBulk>& ctx) {
            int32_t max = rand_bulk_size();
            std::vector<int32_t> elements(max);
            size_t dequeued = workload_context.queue.try_dequeue_bulk(elements.data(), max);
            if (dequeued < static_cast<size_t>(elements.size())) {
                elements.resize(dequeued);
            }
            std::vector<int32_t> producer_threads;
            if (dequeued > 0) {
                if (auto resolved = workload_context.resolve_producers_for_bulk(elements.data(), dequeued)) {
                    producer_threads = std::move(*resolved);
                }
            }
            ctx.op = ConcurrentQueueAPI::QueueTryDequeueBulk{elements, max, static_cast<int32_t>(dequeued)};
            std::map<std::string, omnilink::Packable> meta{
                {"consumer_thread", static_cast<int32_t>(thread_idx)}
            };
            if (!producer_threads.empty()) {
                meta["producer_threads"] = producer_threads;
                ctx.op.producers = producer_threads;
            } else {
                ctx.op.producers = std::vector<int32_t>{};
            }
            ctx.op._meta = std::move(meta);
        }

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
        }
    };
};

int main() {
    return QueueWorkloadContext::main();
}

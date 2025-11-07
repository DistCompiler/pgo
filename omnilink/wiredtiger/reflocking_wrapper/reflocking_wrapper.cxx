#include "reflocking_wrapper.h"

#include <omnilink/logger.hpp>
#include <omnilink/models/RefLocking.hpp>

using _logger = omnilink::logger<RefLocking::AnyOperation>;

// #ifdef __cplusplus
// extern "C" {
// #endif

void omnilink_reflocking_wrapper_lock_start() {
    _logger::template start_operation<RefLocking::Lock>();
}

void omnilink_reflocking_wrapper_lock_end(uint64_t owner, uint64_t lock) {
    auto& op = _logger::template ongoing_operation<RefLocking::Lock>();

    _logger::template end_operation<RefLocking::Lock>();
}

void omnilink_reflocking_wrapper_unlock_start() {
    _logger::template start_operation<RefLocking::Unlock>();
}

void omnilink_reflocking_wrapper_unlock_end(uint64_t owner, uint64_t lock) {
    auto& op = _logger::template ongoing_operation<RefLocking::Unlock>();
    op.owner = owner;
    op.lock = lock;
    _logger::template end_operation<RefLocking::Unlock>();
}

// #ifdef __cplusplus
// }
// #endif

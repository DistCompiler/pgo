#include "reflocking_wrapper.h"

#include <omnilink/logger.hpp>
#include <omnilink/models/RefLocking.hpp>
#include <string>

using _logger = omnilink::logger<RefLocking::AnyOperation>;

// #ifdef __cplusplus
// extern "C" {
// #endif

void omnilink_reflocking_wrapper_lock_start(intptr_t owner, intptr_t lock) {
    auto& op = _logger::template start_operation<RefLocking::Lock>();
    op.owner = std::to_string(owner);
    op.lock = std::to_string(lock);
}

void omnilink_reflocking_wrapper_lock_end() {
    _logger::template end_operation<RefLocking::Lock>();
}

void omnilink_reflocking_wrapper_unlock_start(intptr_t owner, intptr_t lock) {
    auto& op = _logger::template start_operation<RefLocking::Unlock>();
    op.owner = std::to_string(owner);
    op.lock = std::to_string(lock);
}

void omnilink_reflocking_wrapper_unlock_end() {
    _logger::template end_operation<RefLocking::Unlock>();
}

// #ifdef __cplusplus
// }
// #endif

#pragma once

#include <cstdint>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

void omnilink_reflocking_wrapper_lock_start();
void omnilink_reflocking_wrapper_lock_end(uint64_t owner, uint64_t lock);

void omnilink_reflocking_wrapper_unlock_start();
void omnilink_reflocking_wrapper_unlock_end(uint64_t owner, uint64_t lock);

#ifdef __cplusplus
}
#endif
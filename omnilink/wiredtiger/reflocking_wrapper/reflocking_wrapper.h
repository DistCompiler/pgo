#pragma once

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

void omnilink_reflocking_wrapper_lock_start(intptr_t owner, intptr_t lock);
void omnilink_reflocking_wrapper_lock_end();
void omnilink_reflocking_wrapper_lock_abort();

void omnilink_reflocking_wrapper_unlock_start(intptr_t owner, intptr_t lock);
void omnilink_reflocking_wrapper_unlock_end();
void omnilink_reflocking_wrapper_unlock_abort();

void omnilink_reflocking_wrapper_bug();

#ifdef __cplusplus
}
#endif
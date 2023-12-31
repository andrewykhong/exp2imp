/*
Copyright (c) 2019, Lawrence Livermore National Security, LLC
and DESUL project contributors. See the COPYRIGHT file for details.
Source: https://github.com/desul/desul

SPDX-License-Identifier: (BSD-3-Clause)
*/

#ifndef DESUL_ATOMICS_LOCK_ARRAY_HPP_
#define DESUL_ATOMICS_LOCK_ARRAY_HPP_

#include <desul/atomics/Compare_Exchange.hpp>
#include <desul/atomics/Macros.hpp>
#ifdef DESUL_HAVE_CUDA_ATOMICS
#include <desul/atomics/Lock_Array_CUDA.hpp>
#endif
#ifdef DESUL_HAVE_HIP_ATOMICS
#include <desul/atomics/Lock_Array_HIP.hpp>
#endif

namespace desul {
namespace Impl {

struct HostLocks {
  static constexpr uint32_t HOST_SPACE_ATOMIC_MASK = 0xFFFF;
  static constexpr uint32_t HOST_SPACE_ATOMIC_XOR_MASK = 0x5A39;
  template <class is_always_void = void>
  static int32_t* get_host_locks_() {
    static int32_t HOST_SPACE_ATOMIC_LOCKS_DEVICE[HOST_SPACE_ATOMIC_MASK + 1] = {};
    return HOST_SPACE_ATOMIC_LOCKS_DEVICE;
  }
  static inline int32_t* get_host_lock_(void* ptr) {
    return &get_host_locks_()[((uint64_t(ptr) >> 2) & HOST_SPACE_ATOMIC_MASK) ^
                              HOST_SPACE_ATOMIC_XOR_MASK];
  }
};

inline void init_lock_arrays() {
  static bool is_initialized = false;
  if (!is_initialized) {
    HostLocks::get_host_locks_();
    is_initialized = true;
  }

#ifdef DESUL_HAVE_CUDA_ATOMICS
  init_lock_arrays_cuda();
#endif

#ifdef DESUL_HAVE_HIP_ATOMICS
  init_lock_arrays_hip();
#endif
}

inline void finalize_lock_arrays() {
#ifdef DESUL_HAVE_CUDA_ATOMICS
  finalize_lock_arrays_cuda();
#endif

#ifdef DESUL_HAVE_HIP_ATOMICS
  finalize_lock_arrays_hip();
#endif
}

inline void ensure_lock_arrays_on_device() {
#ifdef DESUL_HAVE_CUDA_ATOMICS
  ensure_cuda_lock_arrays_on_device();
#endif

#ifdef DESUL_HAVE_HIP_ATOMICS
  DESUL_ENSURE_HIP_LOCK_ARRAYS_ON_DEVICE();
#endif
}

template <class MemoryScope>
bool lock_address(void* ptr, MemoryScope ms) {
  return 0 == atomic_exchange(
                  HostLocks::get_host_lock_(ptr), int32_t(1), MemoryOrderSeqCst(), ms);
}

template <class MemoryScope>
void unlock_address(void* ptr, MemoryScope ms) {
  (void)atomic_exchange(
      HostLocks::get_host_lock_(ptr), int32_t(0), MemoryOrderSeqCst(), ms);
}

}  // namespace Impl
}  // namespace desul

#endif  // DESUL_ATOMICS_LOCK_ARRAY_HPP_

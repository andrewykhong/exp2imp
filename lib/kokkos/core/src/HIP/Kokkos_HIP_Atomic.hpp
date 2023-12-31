//@HEADER
// ************************************************************************
//
//                        Kokkos v. 4.0
//       Copyright (2022) National Technology & Engineering
//               Solutions of Sandia, LLC (NTESS).
//
// Under the terms of Contract DE-NA0003525 with NTESS,
// the U.S. Government retains certain rights in this software.
//
// Part of Kokkos, under the Apache License v2.0 with LLVM Exceptions.
// See https://kokkos.org/LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//@HEADER

#ifndef KOKKOS_HIP_ATOMIC_HPP
#define KOKKOS_HIP_ATOMIC_HPP

#include <impl/Kokkos_Atomic_Memory_Order.hpp>
#include <impl/Kokkos_Memory_Fence.hpp>
#include <HIP/Kokkos_HIP_Locks.hpp>

#if defined(KOKKOS_ENABLE_HIP_ATOMICS)
namespace Kokkos {
// HIP can do:
// Types int/unsigned int
// variants:
// atomic_exchange/compare_exchange/fetch_add/fetch_sub/fetch_max/fetch_min/fetch_and/fetch_or/fetch_xor/fetch_inc/fetch_dec

// atomic_exchange -------------------------------------------------------------

__inline__ __device__ int atomic_exchange(volatile int *const dest,
                                          const int val) {
  return atomicExch(const_cast<int *>(dest), val);
}

__inline__ __device__ unsigned int atomic_exchange(
    volatile unsigned int *const dest, const unsigned int val) {
  return atomicExch(const_cast<unsigned int *>(dest), val);
}

__inline__ __device__ unsigned long long int atomic_exchange(
    volatile unsigned long long int *const dest,
    const unsigned long long int val) {
  return atomicExch(const_cast<unsigned long long *>(dest), val);
}

__inline__ __device__ float atomic_exchange(volatile float *const dest,
                                            const float val) {
  return atomicExch(const_cast<float *>(dest), val);
}

template <typename T>
__inline__ __device__ T
atomic_exchange(volatile T *const dest,
                std::enable_if_t<sizeof(T) == sizeof(int), const T &> val) {
  int tmp = atomicExch(reinterpret_cast<int *>(const_cast<T *>(dest)),
                       *reinterpret_cast<int *>(const_cast<T *>(&val)));
  return reinterpret_cast<T &>(tmp);
}

template <typename T>
__inline__ __device__ T atomic_exchange(
    volatile T *const dest,
    std::enable_if_t<sizeof(T) != sizeof(int) &&
                         sizeof(T) == sizeof(unsigned long long int),
                     const T &>
        val) {
  using type = unsigned long long int;

  type tmp = atomicExch(reinterpret_cast<type *>(const_cast<T *>(dest)),
                        *reinterpret_cast<type *>(const_cast<T *>(&val)));
  return reinterpret_cast<T &>(tmp);
}

template <typename T>
__inline__ __device__ T atomic_exchange(
    volatile T *const dest,
    std::enable_if_t<sizeof(T) != sizeof(int) && sizeof(T) != sizeof(long long),
                     const T> &val) {
  T return_val;
  int done                 = 0;
  unsigned int active      = __ballot(1);
  unsigned int done_active = 0;
  while (active != done_active) {
    if (!done) {
      if (Impl::lock_address_hip_space((void *)dest)) {
        return_val = *dest;
        *dest      = val;
        Impl::unlock_address_hip_space((void *)dest);
        done = 1;
      }
    }
    done_active = __ballot(done);
  }
  return return_val;
}

// atomic_assign ---------------------------------------------------------------

template <typename T>
__inline__ __device__ void atomic_assign(
    volatile T *const dest,
    std::enable_if_t<sizeof(T) == sizeof(int), const T &> val) {
  atomicExch(reinterpret_cast<int *>(const_cast<T *>(dest)),
             *reinterpret_cast<int *>(const_cast<T *>(&val)));
}

template <typename T>
__inline__ __device__ void atomic_assign(
    volatile T *const dest,
    std::enable_if_t<sizeof(T) != sizeof(int) &&
                         sizeof(T) == sizeof(unsigned long long int),
                     const T &>
        val) {
  using type = unsigned long long int;
  atomicExch(reinterpret_cast<type *>(const_cast<T *>(dest)),
             *reinterpret_cast<type *>(const_cast<T *>(&val)));
}

template <typename T>
__inline__ __device__ void atomic_assign(
    volatile T *const dest,
    std::enable_if_t<sizeof(T) != sizeof(int) &&
                         sizeof(T) != sizeof(unsigned long long int),
                     const T &>
        val) {
  atomic_exchange(dest, val);
}

// atomic_compare_exchange -----------------------------------------------------

inline __device__ int atomic_compare_exchange(volatile int *dest, int compare,
                                              const int &val) {
  return atomicCAS(const_cast<int *>(dest), compare, val);
}

inline __device__ unsigned int atomic_compare_exchange(
    volatile unsigned int *dest, unsigned int compare,
    const unsigned int &val) {
  return atomicCAS(const_cast<unsigned int *>(dest), compare, val);
}

inline __device__ unsigned long long int atomic_compare_exchange(
    volatile unsigned long long int *dest, unsigned long long int compare,
    const unsigned long long int &val) {
  return atomicCAS(const_cast<unsigned long long int *>(dest), compare, val);
}

template <class T>
__inline__ __device__ T atomic_compare_exchange(
    volatile T *dest, T compare,
    std::enable_if_t<sizeof(T) == sizeof(int), const T &> val) {
  // FIXME_HIP UB
  union U {
    int i;
    T f;
    __inline__ __device__ U() {}
  } idest, icompare, ival;
  icompare.f = compare;
  ival.f     = val;
  idest.i    = atomicCAS(reinterpret_cast<int *>(const_cast<T *>(dest)),
                      icompare.i, ival.i);
  return idest.f;
}

template <class T>
__inline__ __device__ T atomic_compare_exchange(
    volatile T *dest, T compare,
    std::enable_if_t<sizeof(T) == sizeof(unsigned long long int), const T &>
        val) {
  // FIXME_HIP UB
  union U {
    unsigned long long int i;
    T f;
    __inline__ __device__ U() {}
  } idest, icompare, ival;
  icompare.f = compare;
  ival.f     = val;
  idest.i    = atomicCAS(
      reinterpret_cast<unsigned long long int *>(const_cast<T *>(dest)),
      icompare.i, ival.i);
  return idest.f;
}

template <typename T>
__inline__ __device__ T atomic_compare_exchange(
    volatile T *const dest, const T &compare,
    std::enable_if_t<sizeof(T) != sizeof(int) && sizeof(T) != sizeof(long long),
                     const T> &val) {
  T return_val;
  int done                 = 0;
  unsigned int active      = __ballot(1);
  unsigned int done_active = 0;
  while (active != done_active) {
    if (!done) {
      if (Impl::lock_address_hip_space((void *)dest)) {
        return_val = *dest;
        if (return_val == compare) *dest = val;
        Impl::unlock_address_hip_space((void *)dest);
        done = 1;
      }
    }
    done_active = __ballot(done);
  }
  return return_val;
}

// atomic_fetch_add ------------------------------------------------------------

inline __device__ int atomic_fetch_add(volatile int *dest, const int &val) {
  return atomicAdd(const_cast<int *>(dest), val);
}

inline __device__ unsigned int atomic_fetch_add(volatile unsigned int *dest,
                                                const unsigned int &val) {
  return atomicAdd(const_cast<unsigned int *>(dest), val);
}

inline __device__ unsigned long long atomic_fetch_add(
    volatile unsigned long long *dest, const unsigned long long &val) {
  return atomicAdd(const_cast<unsigned long long *>(dest), val);
}

inline __device__ float atomic_fetch_add(volatile float *dest,
                                         const float &val) {
  return atomicAdd(const_cast<float *>(dest), val);
}

template <typename T>
inline __device__ T
atomic_fetch_add(volatile T *const dest,
                 std::enable_if_t<sizeof(T) == sizeof(int), const T> val) {
  // FIXME_HIP UB
  union U {
    int i;
    T t;
    __inline__ __device__ U() {}
  } assume, oldval, newval;

  oldval.t = *dest;

  do {
    assume.i = oldval.i;
    newval.t = assume.t + val;
    oldval.i = atomicCAS(reinterpret_cast<int *>(const_cast<T *>(dest)),
                         assume.i, newval.i);
  } while (assume.i != oldval.i);

  return oldval.t;
}

template <typename T>
inline __device__ T atomic_fetch_add(
    volatile T *const dest,
    std::enable_if_t<sizeof(T) == sizeof(long long), const T> val) {
  // FIXME_HIP UB
  union U {
    unsigned long long i;
    T t;
    __inline__ __device__ U() {}
  } assume, oldval, newval;

  oldval.t = *dest;

  do {
    assume.i = oldval.i;
    newval.t = assume.t + val;
    oldval.i = atomic_compare_exchange(
        reinterpret_cast<volatile unsigned long long *>(dest), assume.i,
        newval.i);
  } while (assume.i != oldval.i);

  return oldval.t;
}

__inline__ __device__ char atomic_fetch_add(volatile char *dest,
                                            const char &val) {
  unsigned int oldval, newval, assume;
  oldval = *reinterpret_cast<volatile unsigned int *>(&dest);

  do {
    assume = oldval;
    newval = assume & 0x7fffff00 + ((assume & 0xff) + val) & 0xff;
    oldval =
        atomicCAS(reinterpret_cast<unsigned int *>(const_cast<char *>(dest)),
                  assume, newval);
  } while (assume != oldval);

  return oldval;
}

__inline__ __device__ short atomic_fetch_add(volatile short *dest,
                                             const short &val) {
  unsigned int oldval, newval, assume;
  oldval = *reinterpret_cast<volatile unsigned int *>(&dest);

  do {
    assume = oldval;
    newval = assume & 0x7fff0000 + ((assume & 0xffff) + val) & 0xffff;
    oldval =
        atomicCAS(reinterpret_cast<unsigned int *>(const_cast<short *>(dest)),
                  assume, newval);
  } while (assume != oldval);

  return oldval;
}

__inline__ __device__ long long atomic_fetch_add(volatile long long *dest,
                                                 const long long &val) {
  return atomicAdd(
      reinterpret_cast<unsigned long long *>(const_cast<long long *>(dest)),
      val);
}

template <class T>
__inline__ __device__ T atomic_fetch_add(
    volatile T *dest,
    std::enable_if_t<sizeof(T) != sizeof(int) && sizeof(T) != sizeof(long long),
                     const T &>
        val) {
  T return_val;
  int done                 = 0;
  unsigned int active      = __ballot(1);
  unsigned int done_active = 0;
  while (active != done_active) {
    if (!done) {
      if (Kokkos::Impl::lock_address_hip_space((void *)dest)) {
        return_val = *dest;
        *dest      = return_val + val;
        Kokkos::Impl::unlock_address_hip_space((void *)dest);
        done = 1;
      }
    }
    done_active = __ballot(done);
  }
  return return_val;
}

// atmic_fetch_sub -------------------------------------------------------------

__inline__ __device__ int atomic_fetch_sub(volatile int *dest, int const &val) {
  return atomicSub(const_cast<int *>(dest), val);
}

__inline__ __device__ unsigned int atomic_fetch_sub(volatile unsigned int *dest,
                                                    unsigned int const &val) {
  return atomicSub(const_cast<unsigned int *>(dest), val);
}

__inline__ __device__ unsigned long long atomic_fetch_sub(
    unsigned long long *dest, int64_t const &val) {
  return atomicAdd(reinterpret_cast<unsigned long long *>(dest),
                   -reinterpret_cast<unsigned long long const &>(val));
}

__inline__ __device__ char atomic_fetch_sub(volatile char *dest,
                                            const char &val) {
  unsigned int oldval, newval, assume;
  oldval = *reinterpret_cast<volatile unsigned int *>(dest);

  do {
    assume = oldval;
    newval = assume & 0x7fffff00 + ((assume & 0xff) - val) & 0xff;
    oldval =
        atomicCAS(reinterpret_cast<unsigned int *>(const_cast<char *>(dest)),
                  assume, newval);
  } while (assume != oldval);

  return oldval;
}

__inline__ __device__ short atomic_fetch_sub(volatile short *dest,
                                             const short &val) {
  unsigned int oldval, newval, assume;
  oldval = *reinterpret_cast<volatile unsigned int *>(dest);

  do {
    assume = oldval;
    newval = assume & 0x7fff0000 + ((assume & 0xffff) - val) & 0xffff;
    oldval =
        atomicCAS(reinterpret_cast<unsigned int *>(const_cast<short *>(dest)),
                  assume, newval);
  } while (assume != oldval);

  return oldval;
}

__inline__ __device__ long long atomic_fetch_sub(volatile long long *dest,
                                                 const long long &val) {
  return static_cast<long long>(atomicAdd(
      reinterpret_cast<unsigned long long int *>(const_cast<long long *>(dest)),
      -reinterpret_cast<unsigned long long int const &>(val)));
}

template <class T>
__inline__ __device__ T atomic_fetch_sub(
    volatile T *dest, std::enable_if_t<sizeof(T) == sizeof(int), T> val) {
  // FIXME_HIP UB
  union U {
    int i;
    T t;
    __inline__ __device__ U() {}
  } assume, oldval, newval;

  oldval.t = *dest;

  do {
    assume.i = oldval.i;
    newval.t = assume.t - val;
    oldval.i = atomic_compare_exchange(reinterpret_cast<volatile int *>(dest),
                                       assume.i, newval.i);
  } while (assume.i != oldval.i);

  return oldval.t;
}

template <typename T>
inline __device__ T atomic_fetch_sub(
    volatile T *const dest,
    std::enable_if_t<sizeof(T) == sizeof(long long), const T> val) {
  // FIXME_HIP UB
  union U {
    unsigned long long i;
    T t;
    __inline__ __device__ U() {}
  } assume, oldval, newval;

  oldval.t = *dest;

  do {
    assume.i = oldval.i;
    newval.t = assume.t - val;
    oldval.i = atomic_compare_exchange(
        reinterpret_cast<volatile unsigned long long *>(dest), assume.i,
        newval.i);
  } while (assume.i != oldval.i);

  return oldval.t;
}

template <class T>
__inline__ __device__ T atomic_fetch_sub(
    volatile T *dest, std::enable_if_t<sizeof(T) == sizeof(char), T> val) {
  unsigned int oldval, newval, assume;
  oldval = *reinterpret_cast<volatile unsigned int *>(dest);

  do {
    assume = oldval;
    newval = assume & 0x7fffff00 + ((assume & 0xff) - val) & 0xff;
    oldval = atomicCAS(reinterpret_cast<unsigned int *>(dest), assume, newval);
  } while (assume != oldval);

  return reinterpret_cast<T>(oldval) & 0xff;
}

template <class T>
__inline__ __device__ T atomic_fetch_sub(
    volatile T *dest, std::enable_if_t<sizeof(T) == sizeof(short), T> val) {
  unsigned int oldval, newval, assume;
  oldval = *reinterpret_cast<int *>(dest);

  do {
    assume = oldval;
    newval = assume & 0x7fff0000 + ((assume & 0xffff) - val) & 0xffff;
    oldval = atomicCAS(reinterpret_cast<unsigned int *>(dest), assume, newval);
  } while (assume != oldval);

  return reinterpret_cast<T>(oldval) & 0xffff;
}

template <typename T>
__inline__ __device__ T atomic_fetch_sub(
    volatile T *const dest,
    std::enable_if_t<sizeof(T) != sizeof(int) && sizeof(T) != sizeof(long long),
                     const T> &val) {
  T return_val;
  int done                 = 0;
  unsigned int active      = __ballot(1);
  unsigned int done_active = 0;
  while (active != done_active) {
    if (!done) {
      if (Impl::lock_address_hip_space((void *)dest)) {
        return_val = *dest;
        *dest      = return_val - val;
        Impl::unlock_address_hip_space((void *)dest);
        done = 1;
      }
    }
    done_active = __ballot(done);
  }
  return return_val;
}

// atomic_fetch_or -------------------------------------------------------------

__inline__ __device__ int atomic_fetch_or(volatile int *const dest,
                                          int const val) {
  return atomicOr(const_cast<int *>(dest), val);
}

__inline__ __device__ unsigned int atomic_fetch_or(
    volatile unsigned int *const dest, unsigned int const val) {
  return atomicOr(const_cast<unsigned int *>(dest), val);
}

__inline__ __device__ unsigned long long int atomic_fetch_or(
    volatile unsigned long long int *const dest,
    unsigned long long int const val) {
  return atomicOr(const_cast<unsigned long long int *>(dest), val);
}

// atomic_fetch_and ------------------------------------------------------------

__inline__ __device__ int atomic_fetch_and(volatile int *const dest,
                                           int const val) {
  return atomicAnd(const_cast<int *>(dest), val);
}

__inline__ __device__ unsigned int atomic_fetch_and(
    volatile unsigned int *const dest, unsigned int const val) {
  return atomicAnd(const_cast<unsigned int *>(dest), val);
}

__inline__ __device__ unsigned long long int atomic_fetch_and(
    volatile unsigned long long int *const dest,
    unsigned long long int const val) {
  return atomicAnd(const_cast<unsigned long long int *>(dest), val);
}

namespace Impl {

template <typename T>
__inline__ __device__ void _atomic_store(T *ptr, T val,
                                         memory_order_relaxed_t) {
  (void)atomic_exchange(ptr, val);
}

template <typename T>
__inline__ __device__ void _atomic_store(T *ptr, T val,
                                         memory_order_seq_cst_t) {
  memory_fence();
  atomic_store(ptr, val, memory_order_relaxed);
  memory_fence();
}

template <typename T>
__inline__ __device__ void _atomic_store(T *ptr, T val,
                                         memory_order_release_t) {
  memory_fence();
  atomic_store(ptr, val, memory_order_relaxed);
}

template <typename T>
__inline__ __device__ void _atomic_store(T *ptr, T val) {
  atomic_store(ptr, val, memory_order_relaxed);
}

template <typename T>
__inline__ __device__ T _atomic_load(T *ptr, memory_order_relaxed_t) {
  T dummy{};
  return atomic_compare_exchange(ptr, dummy, dummy);
}

template <typename T>
__inline__ __device__ T _atomic_load(T *ptr, memory_order_seq_cst_t) {
  memory_fence();
  T rv = atomic_load(ptr, memory_order_relaxed);
  memory_fence();
  return rv;
}

template <typename T>
__inline__ __device__ T _atomic_load(T *ptr, memory_order_acquire_t) {
  T rv = atomic_load(ptr, memory_order_relaxed);
  memory_fence();
  return rv;
}

template <typename T>
__inline__ __device__ T _atomic_load(T *ptr) {
  return atomic_load(ptr, memory_order_relaxed);
}

}  // namespace Impl
}  // namespace Kokkos
#endif

#endif

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

#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
#include <xmmintrin.h>
#endif

#include <Kokkos_Macros.hpp>
#if defined(KOKKOS_ATOMIC_HPP) && !defined(KOKKOS_ATOMIC_FETCH_ADD_HPP)
#define KOKKOS_ATOMIC_FETCH_ADD_HPP

namespace Kokkos {

//----------------------------------------------------------------------------

#if defined(KOKKOS_ENABLE_CUDA)
#if defined(__CUDA_ARCH__) || defined(KOKKOS_IMPL_CUDA_CLANG_WORKAROUND)

// Support for int, unsigned int, unsigned long long int, and float

__inline__ __device__ int atomic_fetch_add(volatile int* const dest,
                                           const int val) {
  return atomicAdd((int*)dest, val);
}

__inline__ __device__ unsigned int atomic_fetch_add(
    volatile unsigned int* const dest, const unsigned int val) {
  return atomicAdd((unsigned int*)dest, val);
}

__inline__ __device__ unsigned long long int atomic_fetch_add(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  return atomicAdd((unsigned long long int*)dest, val);
}

__inline__ __device__ float atomic_fetch_add(volatile float* const dest,
                                             const float val) {
  return atomicAdd((float*)dest, val);
}

#if (600 <= __CUDA_ARCH__)
__inline__ __device__ double atomic_fetch_add(volatile double* const dest,
                                              const double val) {
  return atomicAdd((double*)dest, val);
}
#endif

template <typename T>
__inline__ __device__ T
atomic_fetch_add(volatile T* const dest,
                 std::enable_if_t<sizeof(T) == sizeof(int), const T> val) {
  // to work around a bug in the clang cuda compiler, the name here needs to be
  // different from the one internal to the other overloads
  union U1 {
    int i;
    T t;
    KOKKOS_INLINE_FUNCTION U1() {}
  } assume, oldval, newval;

  oldval.t = *dest;

  do {
    assume.i = oldval.i;
    newval.t = assume.t + val;
    oldval.i = atomicCAS((int*)dest, assume.i, newval.i);
  } while (assume.i != oldval.i);

  return oldval.t;
}

template <typename T>
__inline__ __device__ T atomic_fetch_add(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) != sizeof(int) &&
                         sizeof(T) == sizeof(unsigned long long int),
                     const T>
        val) {
  // to work around a bug in the clang cuda compiler, the name here needs to be
  // different from the one internal to the other overloads
  union U2 {
    unsigned long long int i;
    T t;
    KOKKOS_INLINE_FUNCTION U2() {}
  } assume, oldval, newval;

  oldval.t = *dest;

  do {
    assume.i = oldval.i;
    newval.t = assume.t + val;
    oldval.i = atomicCAS((unsigned long long int*)dest, assume.i, newval.i);
  } while (assume.i != oldval.i);

  return oldval.t;
}

//----------------------------------------------------------------------------

template <typename T>
__inline__ __device__ T atomic_fetch_add(
    volatile T* const dest,
    std::enable_if_t<(sizeof(T) != 4) && (sizeof(T) != 8), const T>& val) {
  T return_val;
  // This is a way to (hopefully) avoid dead lock in a warp
  int done                 = 0;
  unsigned int mask        = __activemask();
  unsigned int active      = __ballot_sync(mask, 1);
  unsigned int done_active = 0;
  while (active != done_active) {
    if (!done) {
      bool locked = Impl::lock_address_cuda_space((void*)dest);
      if (locked) {
        Kokkos::memory_fence();
        return_val = *dest;
        *dest      = return_val + val;
        Kokkos::memory_fence();
        Impl::unlock_address_cuda_space((void*)dest);
        done = 1;
      }
    }

    done_active = __ballot_sync(mask, done);
  }
  return return_val;
}
#endif
#endif
//----------------------------------------------------------------------------
#if !defined(__CUDA_ARCH__) || defined(KOKKOS_IMPL_CUDA_CLANG_WORKAROUND)
#if defined(KOKKOS_ENABLE_GNU_ATOMICS) || defined(KOKKOS_ENABLE_INTEL_ATOMICS)

#if defined(KOKKOS_ENABLE_ASM) && defined(KOKKOS_ENABLE_ISA_X86_64)
inline int atomic_fetch_add(volatile int* dest, const int val) {
#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif

  int original = val;

  __asm__ __volatile__("lock xadd %1, %0"
                       : "+m"(*dest), "+r"(original)
                       : "m"(*dest), "r"(original)
                       : "memory");

  return original;
}
#else
inline int atomic_fetch_add(volatile int* const dest, const int val) {
#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif
  return __sync_fetch_and_add(dest, val);
}
#endif

inline long int atomic_fetch_add(volatile long int* const dest,
                                 const long int val) {
#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif
  return __sync_fetch_and_add(dest, val);
}

#if defined(KOKKOS_ENABLE_GNU_ATOMICS)

inline unsigned int atomic_fetch_add(volatile unsigned int* const dest,
                                     const unsigned int val) {
#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif
  return __sync_fetch_and_add(dest, val);
}

inline unsigned long int atomic_fetch_add(
    volatile unsigned long int* const dest, const unsigned long int val) {
#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif
  return __sync_fetch_and_add(dest, val);
}

inline unsigned long long int atomic_fetch_add(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif
  return __sync_fetch_and_add(dest, val);
}

#endif

template <typename T>
inline T atomic_fetch_add(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) == sizeof(int), const T> val) {
  union U {
    int i;
    T t;
    inline U() {}
  } assume, oldval, newval;

#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif

  oldval.t = *dest;

  do {
    assume.i = oldval.i;
    newval.t = assume.t + val;
    oldval.i = __sync_val_compare_and_swap((int*)dest, assume.i, newval.i);
  } while (assume.i != oldval.i);

  return oldval.t;
}

template <typename T>
inline T atomic_fetch_add(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) != sizeof(int) && sizeof(T) == sizeof(long),
                     const T>
        val) {
  union U {
    long i;
    T t;
    inline U() {}
  } assume, oldval, newval;

#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif

  oldval.t = *dest;

  do {
    assume.i = oldval.i;
    newval.t = assume.t + val;
    oldval.i = __sync_val_compare_and_swap((long*)dest, assume.i, newval.i);
  } while (assume.i != oldval.i);

  return oldval.t;
}

#if defined(KOKKOS_ENABLE_ASM) && defined(KOKKOS_ENABLE_ISA_X86_64)
template <typename T>
inline T atomic_fetch_add(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) != sizeof(int) && sizeof(T) != sizeof(long) &&
                         sizeof(T) == sizeof(Impl::cas128_t),
                     const T>
        val) {
  union U {
    Impl::cas128_t i;
    T t;
    inline U() {}
  } assume, oldval, newval;

#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif

  oldval.t = *dest;

  do {
    assume.i = oldval.i;
    newval.t = assume.t + val;
    oldval.i = Impl::cas128((volatile Impl::cas128_t*)dest, assume.i, newval.i);
  } while (assume.i != oldval.i);

  return oldval.t;
}
#endif

//----------------------------------------------------------------------------

template <typename T>
inline T atomic_fetch_add(volatile T* const dest,
                          std::enable_if_t<(sizeof(T) != 4) && (sizeof(T) != 8)
#if defined(KOKKOS_ENABLE_ASM) && defined(KOKKOS_ENABLE_ISA_X86_64)
                                               && (sizeof(T) != 16)
#endif
                                               ,
                                           const T>& val) {
  while (!Impl::lock_address_host_space((void*)dest))
    ;
  Kokkos::memory_fence();
  T return_val = *dest;

  // Don't use the following line of code here:
  //
  // const T tmp = *dest = return_val + val;
  //
  // Instead, put each assignment in its own statement.  This is
  // because the overload of T::operator= for volatile *this should
  // return void, not volatile T&.  See Kokkos #177:
  //
  // https://github.com/kokkos/kokkos/issues/177
  *dest       = return_val + val;
  const T tmp = *dest;
  (void)tmp;
  Kokkos::memory_fence();
  Impl::unlock_address_host_space((void*)dest);

  return return_val;
}
//----------------------------------------------------------------------------

#elif defined(KOKKOS_ENABLE_OPENMP_ATOMICS)

template <typename T>
T atomic_fetch_add(volatile T* const dest, const T val) {
  T retval;
#pragma omp atomic capture
  {
    retval = dest[0];
    dest[0] += val;
  }
  return retval;
}

#elif defined(KOKKOS_ENABLE_SERIAL_ATOMICS)

template <typename T>
T atomic_fetch_add(volatile T* const dest_v, std::add_const_t<T> val) {
  T* dest  = const_cast<T*>(dest_v);
  T retval = *dest;
  *dest += val;
  return retval;
}

#endif
#endif
//----------------------------------------------------------------------------

// dummy for non-CUDA Kokkos headers being processed by NVCC
#if defined(__CUDA_ARCH__) && !defined(KOKKOS_ENABLE_CUDA)
template <typename T>
__inline__ __device__ T atomic_fetch_add(volatile T* const,
                                         Kokkos::Impl::type_identity_t<T>) {
  return T();
}
#endif

}  // namespace Kokkos
#endif

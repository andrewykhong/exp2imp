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
#if defined(KOKKOS_ATOMIC_HPP) && !defined(KOKKOS_ATOMIC_EXCHANGE_HPP)
#define KOKKOS_ATOMIC_EXCHANGE_HPP

namespace Kokkos {

//----------------------------------------------------------------------------

#if defined(KOKKOS_ENABLE_CUDA)
#if defined(__CUDA_ARCH__) || defined(KOKKOS_IMPL_CUDA_CLANG_WORKAROUND)

__inline__ __device__ int atomic_exchange(volatile int* const dest,
                                          const int val) {
  // return __iAtomicExch( (int*) dest , val );
  return atomicExch((int*)dest, val);
}

__inline__ __device__ unsigned int atomic_exchange(
    volatile unsigned int* const dest, const unsigned int val) {
  // return __uAtomicExch( (unsigned int*) dest , val );
  return atomicExch((unsigned int*)dest, val);
}

__inline__ __device__ unsigned long long int atomic_exchange(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  // return __ullAtomicExch( (unsigned long long*) dest , val );
  return atomicExch((unsigned long long*)dest, val);
}

/** \brief  Atomic exchange for any type with compatible size */
template <typename T>
__inline__ __device__ T
atomic_exchange(volatile T* const dest,
                std::enable_if_t<sizeof(T) == sizeof(int), const T&> val) {
  // int tmp = __ullAtomicExch( (int*) dest , *((int*)&val) );
#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif

  int tmp = atomicExch(((int*)dest), *((int*)&val));
  return *((T*)&tmp);
}

template <typename T>
__inline__ __device__ T atomic_exchange(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) != sizeof(int) &&
                         sizeof(T) == sizeof(unsigned long long int),
                     const T&>
        val) {
  using type = unsigned long long int;

#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif

  // type tmp = __ullAtomicExch( (type*) dest , *((type*)&val) );
  type tmp = atomicExch(((type*)dest), *((type*)&val));
  return *((T*)&tmp);
}

template <typename T>
__inline__ __device__ T atomic_exchange(
    volatile T* const dest,
    std::enable_if_t<(sizeof(T) != 4) && (sizeof(T) != 8), const T>& val) {
  T return_val;
  // This is a way to (hopefully) avoid dead lock in a warp
#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif

  int done                 = 0;
  unsigned int mask        = __activemask();
  unsigned int active      = __ballot_sync(mask, 1);
  unsigned int done_active = 0;
  while (active != done_active) {
    if (!done) {
      if (Impl::lock_address_cuda_space((void*)dest)) {
        Kokkos::memory_fence();
        return_val = *dest;
        *dest      = val;
        Kokkos::memory_fence();
        Impl::unlock_address_cuda_space((void*)dest);
        done = 1;
      }
    }
    done_active = __ballot_sync(mask, done);
  }
  return return_val;
}
/** \brief  Atomic exchange for any type with compatible size */
template <typename T>
__inline__ __device__ void atomic_assign(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) == sizeof(int), const T&> val) {
  // (void) __ullAtomicExch( (int*) dest , *((int*)&val) );
  (void)atomicExch(((int*)dest), *((int*)&val));
}

template <typename T>
__inline__ __device__ void atomic_assign(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) != sizeof(int) &&
                         sizeof(T) == sizeof(unsigned long long int),
                     const T&>
        val) {
  using type = unsigned long long int;
  // (void) __ullAtomicExch( (type*) dest , *((type*)&val) );
  (void)atomicExch(((type*)dest), *((type*)&val));
}

template <typename T>
__inline__ __device__ void atomic_assign(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) != sizeof(int) &&
                         sizeof(T) != sizeof(unsigned long long int),
                     const T&>
        val) {
  (void)atomic_exchange(dest, val);
}

#endif
#endif

//----------------------------------------------------------------------------

#if !defined(__CUDA_ARCH__) || defined(KOKKOS_IMPL_CUDA_CLANG_WORKAROUND)
#if defined(KOKKOS_ENABLE_GNU_ATOMICS) || defined(KOKKOS_ENABLE_INTEL_ATOMICS)

template <typename T>
inline T atomic_exchange(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) == sizeof(int) || sizeof(T) == sizeof(long),
                     const T&>
        val) {
  using type = std::conditional_t<sizeof(T) == sizeof(int), int, long>;
#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif

  const type v = *((type*)&val);  // Extract to be sure the value doesn't change

  type assumed;

  union U {
    T val_T;
    type val_type;
    inline U() {}
  } old;

  old.val_T = *dest;

  do {
    assumed = old.val_type;
    old.val_type =
        __sync_val_compare_and_swap((volatile type*)dest, assumed, v);
  } while (assumed != old.val_type);

  return old.val_T;
}

#if defined(KOKKOS_ENABLE_ASM) && defined(KOKKOS_ENABLE_ISA_X86_64)
template <typename T>
inline T atomic_exchange(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) == sizeof(Impl::cas128_t), const T&> val) {
#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif

  union U {
    Impl::cas128_t i;
    T t;
    inline U() {}
  } assume, oldval, newval;

  oldval.t = *dest;
  newval.t = val;

  do {
    assume.i = oldval.i;
    oldval.i = Impl::cas128((volatile Impl::cas128_t*)dest, assume.i, newval.i);
  } while (assume.i != oldval.i);

  return oldval.t;
}
#endif

//----------------------------------------------------------------------------

template <typename T>
inline T atomic_exchange(volatile T* const dest,
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
  // const T tmp = *dest = val;
  //
  // Instead, put each assignment in its own statement.  This is
  // because the overload of T::operator= for volatile *this should
  // return void, not volatile T&.  See Kokkos #177:
  //
  // https://github.com/kokkos/kokkos/issues/177
  *dest       = val;
  const T tmp = *dest;
#ifndef KOKKOS_COMPILER_CLANG
  (void)tmp;
#endif
  Kokkos::memory_fence();
  Impl::unlock_address_host_space((void*)dest);
  return return_val;
}

template <typename T>
inline void atomic_assign(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) == sizeof(int) || sizeof(T) == sizeof(long),
                     const T&>
        val) {
  using type = std::conditional_t<sizeof(T) == sizeof(int), int, long>;

#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif

  const type v = *((type*)&val);  // Extract to be sure the value doesn't change

  type assumed;

  union U {
    T val_T;
    type val_type;
    inline U() {}
  } old;

  old.val_T = *dest;

  do {
    assumed = old.val_type;
    old.val_type =
        __sync_val_compare_and_swap((volatile type*)dest, assumed, v);
  } while (assumed != old.val_type);
}

#if defined(KOKKOS_ENABLE_ASM) && defined(KOKKOS_ENABLE_ISA_X86_64)
template <typename T>
inline void atomic_assign(
    volatile T* const dest,
    std::enable_if_t<sizeof(T) == sizeof(Impl::cas128_t), const T&> val) {
#if defined(KOKKOS_ENABLE_RFO_PREFETCH)
  _mm_prefetch((const char*)dest, _MM_HINT_ET0);
#endif

  union U {
    Impl::cas128_t i;
    T t;
    inline U() {}
  } assume, oldval, newval;

  oldval.t = *dest;
  newval.t = val;
  do {
    assume.i = oldval.i;
    oldval.i = Impl::cas128((volatile Impl::cas128_t*)dest, assume.i, newval.i);
  } while (assume.i != oldval.i);
}
#endif

template <typename T>
inline void atomic_assign(volatile T* const dest,
                          std::enable_if_t<(sizeof(T) != 4) && (sizeof(T) != 8)
#if defined(KOKKOS_ENABLE_ASM) && defined(KOKKOS_ENABLE_ISA_X86_64)
                                               && (sizeof(T) != 16)
#endif
                                               ,
                                           const T>& val) {
  while (!Impl::lock_address_host_space((void*)dest))
    ;
  Kokkos::memory_fence();
  // This is likely an aggregate type with a defined
  // 'volatile T & operator = ( const T & ) volatile'
  // member.  The volatile return value implicitly defines a
  // dereference that some compilers (gcc 4.7.2) warn is being ignored.
  // Suppress warning by casting return to void.
  //(void)( *dest = val );
  *dest = val;
  Kokkos::memory_fence();
  Impl::unlock_address_host_space((void*)dest);
}
//----------------------------------------------------------------------------

#elif defined(KOKKOS_ENABLE_OPENMP_ATOMICS)

template <typename T>
inline T atomic_exchange(volatile T* const dest, const T val) {
  T retval;
  //#pragma omp atomic capture
#pragma omp critical
  {
    retval  = dest[0];
    dest[0] = val;
  }
  return retval;
}

template <typename T>
inline void atomic_assign(volatile T* const dest, const T val) {
  //#pragma omp atomic
#pragma omp critical
  { dest[0] = val; }
}

#elif defined(KOKKOS_ENABLE_SERIAL_ATOMICS)

template <typename T>
inline T atomic_exchange(volatile T* const dest_v, const T val) {
  T* dest  = const_cast<T*>(dest_v);
  T retval = *dest;
  *dest    = val;
  return retval;
}

template <typename T>
inline void atomic_assign(volatile T* const dest_v, const T val) {
  T* dest = const_cast<T*>(dest_v);
  *dest   = val;
}

#endif
#endif

// dummy for non-CUDA Kokkos headers being processed by NVCC
#if defined(__CUDA_ARCH__) && !defined(KOKKOS_ENABLE_CUDA)
template <typename T>
__inline__ __device__ T
atomic_exchange(volatile T* const, const Kokkos::Impl::type_identity_t<T>) {
  return T();
}

template <typename T>
__inline__ __device__ void atomic_assign(
    volatile T* const, const Kokkos::Impl::type_identity_t<T>) {}
#endif

}  // namespace Kokkos

#endif

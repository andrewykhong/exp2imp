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

#include <Kokkos_Macros.hpp>
#if defined(KOKKOS_ATOMIC_HPP) && !defined(KOKKOS_ATOMIC_MINMAX_HPP)
#define KOKKOS_ATOMIC_MINMAX_HPP

namespace Kokkos {

//----------------------------------------------------------------------------

#if defined(KOKKOS_ENABLE_CUDA)
#if defined(__CUDA_ARCH__) || defined(KOKKOS_IMPL_CUDA_CLANG_WORKAROUND)

// Support for int, unsigned int, unsigned long long int, and float

// Atomic_fetch_{min,max}

#ifdef KOKKOS_IMPL_CUDA_CLANG_WORKAROUND

// Host implementations for CLANG compiler

inline __host__ int atomic_fetch_min(volatile int* const dest, const int val) {
  return Impl::atomic_fetch_oper(Impl::MinOper<const int, const int>(), dest,
                                 val);
}

inline __host__ unsigned int atomic_fetch_min(volatile unsigned int* const dest,
                                              const unsigned int val) {
  return Impl::atomic_fetch_oper(
      Impl::MinOper<const unsigned int, const unsigned int>(), dest, val);
}

inline __host__ unsigned long long int atomic_fetch_min(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  return Impl::atomic_fetch_oper(Impl::MinOper<const unsigned long long int,
                                               const unsigned long long int>(),
                                 dest, val);
}

inline __host__ int atomic_fetch_max(volatile int* const dest, const int val) {
  return Impl::atomic_fetch_oper(Impl::MaxOper<const int, const int>(), dest,
                                 val);
}

inline __host__ unsigned int atomic_fetch_max(volatile unsigned int* const dest,
                                              const unsigned int val) {
  return Impl::atomic_fetch_oper(
      Impl::MaxOper<const unsigned int, const unsigned int>(), dest, val);
}

inline __host__ unsigned long long int atomic_fetch_max(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  return Impl::atomic_fetch_oper(Impl::MaxOper<const unsigned long long int,
                                               const unsigned long long int>(),
                                 dest, val);
}

#endif

#if (350 > __CUDA_ARCH__)

// Fallback for atomic{Min,Max} for Kepler

inline __device__ int atomic_fetch_min(volatile int* const dest,
                                       const int val) {
  return Impl::atomic_fetch_oper(Impl::MinOper<const int, const int>(), dest,
                                 val);
}

inline __device__ unsigned int atomic_fetch_min(
    volatile unsigned int* const dest, const unsigned int val) {
  return Impl::atomic_fetch_oper(
      Impl::MinOper<const unsigned int, const unsigned int>(), dest, val);
}

inline __device__ unsigned long long int atomic_fetch_min(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  return Impl::atomic_fetch_oper(Impl::MinOper<const unsigned long long int,
                                               const unsigned long long int>(),
                                 dest, val);
}

inline __device__ int atomic_fetch_max(volatile int* const dest,
                                       const int val) {
  return Impl::atomic_fetch_oper(Impl::MaxOper<const int, const int>(), dest,
                                 val);
}

inline __device__ unsigned int atomic_fetch_max(
    volatile unsigned int* const dest, const unsigned int val) {
  return Impl::atomic_fetch_oper(
      Impl::MaxOper<const unsigned int, const unsigned int>(), dest, val);
}

inline __device__ unsigned long long int atomic_fetch_max(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  return Impl::atomic_fetch_oper(Impl::MaxOper<const unsigned long long int,
                                               const unsigned long long int>(),
                                 dest, val);
}

#else  // Supported by devices of compute capability 3.5 and higher

inline __device__ int atomic_fetch_min(volatile int* const dest,
                                       const int val) {
  return atomicMin((int*)dest, val);
}

inline __device__ unsigned int atomic_fetch_min(
    volatile unsigned int* const dest, const unsigned int val) {
  return atomicMin((unsigned int*)dest, val);
}

inline __device__ unsigned long long int atomic_fetch_min(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  return atomicMin((unsigned long long int*)dest, val);
}

inline __device__ int atomic_fetch_max(volatile int* const dest,
                                       const int val) {
  return atomicMax((int*)dest, val);
}

inline __device__ unsigned int atomic_fetch_max(
    volatile unsigned int* const dest, const unsigned int val) {
  return atomicMax((unsigned int*)dest, val);
}

inline __device__ unsigned long long int atomic_fetch_max(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  return atomicMax((unsigned long long int*)dest, val);
}

#endif

// Atomic_{min,max}_fetch

#ifdef KOKKOS_IMPL_CUDA_CLANG_WORKAROUND

// Host implementations for CLANG compiler

inline __host__ int atomic_min_fetch(volatile int* const dest, const int val) {
  return Impl::atomic_oper_fetch(Impl::MinOper<const int, const int>(), dest,
                                 val);
}

inline __host__ unsigned int atomic_min_fetch(volatile unsigned int* const dest,
                                              const unsigned int val) {
  return Impl::atomic_oper_fetch(
      Impl::MinOper<const unsigned int, const unsigned int>(), dest, val);
}

inline __host__ unsigned long long int atomic_min_fetch(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  return Impl::atomic_oper_fetch(Impl::MinOper<const unsigned long long int,
                                               const unsigned long long int>(),
                                 dest, val);
}

inline __host__ int atomic_max_fetch(volatile int* const dest, const int val) {
  return Impl::atomic_oper_fetch(Impl::MaxOper<const int, const int>(), dest,
                                 val);
}

inline __host__ unsigned int atomic_max_fetch(volatile unsigned int* const dest,
                                              const unsigned int val) {
  return Impl::atomic_oper_fetch(
      Impl::MaxOper<const unsigned int, const unsigned int>(), dest, val);
}

inline __host__ unsigned long long int atomic_max_fetch(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  return Impl::atomic_oper_fetch(Impl::MaxOper<const unsigned long long int,
                                               const unsigned long long int>(),
                                 dest, val);
}
#endif

#if (350 > __CUDA_ARCH__)

// Fallback for atomic{Min,Max} for Kepler

inline __device__ int atomic_min_fetch(volatile int* const dest,
                                       const int val) {
  return Impl::atomic_oper_fetch(Impl::MinOper<const int, const int>(), dest,
                                 val);
}

inline __device__ unsigned int atomic_min_fetch(
    volatile unsigned int* const dest, const unsigned int val) {
  return Impl::atomic_oper_fetch(
      Impl::MinOper<const unsigned int, const unsigned int>(), dest, val);
}

inline __device__ unsigned long long int atomic_min_fetch(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  return Impl::atomic_oper_fetch(Impl::MinOper<const unsigned long long int,
                                               const unsigned long long int>(),
                                 dest, val);
}

inline __device__ int atomic_max_fetch(volatile int* const dest,
                                       const int val) {
  return Impl::atomic_oper_fetch(Impl::MaxOper<const int, const int>(), dest,
                                 val);
}

inline __device__ unsigned int atomic_max_fetch(
    volatile unsigned int* const dest, const unsigned int val) {
  return Impl::atomic_oper_fetch(
      Impl::MaxOper<const unsigned int, const unsigned int>(), dest, val);
}

inline __device__ unsigned long long int atomic_max_fetch(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  return Impl::atomic_oper_fetch(Impl::MaxOper<const unsigned long long int,
                                               const unsigned long long int>(),
                                 dest, val);
}

#else  // Supported by devices of compute capability 3.5 and higher

inline __device__ int atomic_min_fetch(volatile int* const dest,
                                       const int val) {
  const int old = atomicMin((int*)dest, val);
  return old < val ? old : val;
}

inline __device__ unsigned int atomic_min_fetch(
    volatile unsigned int* const dest, const unsigned int val) {
  const unsigned int old = atomicMin((unsigned int*)dest, val);
  return old < val ? old : val;
}

inline __device__ unsigned long long int atomic_min_fetch(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  const unsigned long long old = atomicMin((unsigned long long*)dest, val);
  return old < val ? old : val;
}

inline __device__ int atomic_max_fetch(volatile int* const dest,
                                       const int val) {
  const int old = atomicMax((int*)dest, val);
  return old >= val ? old : val;
}

inline __device__ unsigned int atomic_max_fetch(
    volatile unsigned int* const dest, const unsigned int val) {
  const unsigned int old = atomicMax((unsigned int*)dest, val);
  return old >= val ? old : val;
}

inline __device__ unsigned long long int atomic_max_fetch(
    volatile unsigned long long int* const dest,
    const unsigned long long int val) {
  const unsigned long long old = atomicMax((unsigned long long*)dest, val);
  return old >= val ? old : val;
}

#endif

#endif
#endif
}  // namespace Kokkos

#endif

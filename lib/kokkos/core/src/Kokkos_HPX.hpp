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

#ifndef KOKKOS_IMPL_PUBLIC_INCLUDE
#include <Kokkos_Macros.hpp>
static_assert(false,
              "Including non-public Kokkos header files is not allowed.");
#endif
#ifndef KOKKOS_HPX_HPP
#define KOKKOS_HPX_HPP

#include <Kokkos_Macros.hpp>
#if defined(KOKKOS_ENABLE_HPX)

#include <Kokkos_Core_fwd.hpp>

#include <Kokkos_HostSpace.hpp>
#include <cstddef>
#include <iosfwd>

#ifdef KOKKOS_ENABLE_HBWSPACE
#include <Kokkos_HBWSpace.hpp>
#endif

#include <Kokkos_HostSpace.hpp>
#include <Kokkos_Layout.hpp>
#include <Kokkos_MemoryTraits.hpp>
#include <Kokkos_Parallel.hpp>
#include <Kokkos_ScratchSpace.hpp>
#include <Kokkos_TaskScheduler.hpp>
#include <impl/Kokkos_ConcurrentBitset.hpp>
#include <impl/Kokkos_FunctorAnalysis.hpp>
#include <impl/Kokkos_Tools.hpp>
#include <impl/Kokkos_TaskQueue.hpp>
#include <impl/Kokkos_InitializationSettings.hpp>

#include <KokkosExp_MDRangePolicy.hpp>

#include <hpx/local/algorithm.hpp>
#include <hpx/local/barrier.hpp>
#include <hpx/local/condition_variable.hpp>
#include <hpx/local/execution.hpp>
#include <hpx/local/future.hpp>
#include <hpx/local/init.hpp>
#include <hpx/local/mutex.hpp>
#include <hpx/local/runtime.hpp>
#include <hpx/local/thread.hpp>

#include <Kokkos_UniqueToken.hpp>

#include <functional>
#include <iostream>
#include <memory>
#include <sstream>
#include <type_traits>
#include <vector>

// There are currently two different implementations for the parallel dispatch
// functions:
//
// - 0: The HPX way. Unfortunately, this comes with unnecessary
//      overheads at the moment, so there is
// - 1: The manual way. This uses for_loop, but only spawns one task per worker
//      thread. This is significantly faster in most cases.
//
// In the long run 0 should be the preferred implementation, but until HPX is
// improved 1 will be the default.
#ifndef KOKKOS_HPX_IMPLEMENTATION
#define KOKKOS_HPX_IMPLEMENTATION 1
#endif

#if (KOKKOS_HPX_IMPLEMENTATION < 0) || (KOKKOS_HPX_IMPLEMENTATION > 1)
#error "You have chosen an invalid value for KOKKOS_HPX_IMPLEMENTATION"
#endif

// [note 1]
//
// When using the asynchronous backend and independent instances, we explicitly
// reset the shared data at the end of a parallel task (execute_task). We do
// this to avoid circular references with shared pointers that would otherwise
// never be released.
//
// The HPX instance holds shared data for the instance in a shared_ptr. One of
// the pieces of shared data is the future that we use to sequence parallel
// dispatches. When a parallel task is launched, a copy of the closure
// (ParallelFor, ParallelReduce, etc.) is captured in the task. The closure
// also holds the policy, the policy holds the HPX instance, the instance holds
// the shared data (for use of buffers in the parallel task). When attaching a
// continuation to a future, the continuation is stored in the future (shared
// state). This means that there is a cycle future -> continuation -> closure
// -> policy -> HPX -> shared data -> future. We break this by releasing the
// shared data early, as (the pointer to) the shared data will not be used
// anymore by the closure at the end of execute_task.
//
// We also mark the shared instance data as mutable so that we can reset it
// from the const execute_task member function.

namespace Kokkos {
namespace Impl {
class thread_buffer {
  static constexpr std::size_t m_cache_line_size = 64;

  std::size_t m_num_threads;
  std::size_t m_size_per_thread;
  std::size_t m_size_total;
  char *m_data;

  void pad_to_cache_line(std::size_t &size) {
    size = ((size + m_cache_line_size - 1) / m_cache_line_size) *
           m_cache_line_size;
  }

 public:
  thread_buffer()
      : m_num_threads(0),
        m_size_per_thread(0),
        m_size_total(0),
        m_data(nullptr) {}
  thread_buffer(const std::size_t num_threads,
                const std::size_t size_per_thread) {
    resize(num_threads, size_per_thread);
  }
  ~thread_buffer() { delete[] m_data; }

  thread_buffer(const thread_buffer &) = delete;
  thread_buffer(thread_buffer &&)      = delete;
  thread_buffer &operator=(const thread_buffer &) = delete;
  thread_buffer &operator=(thread_buffer) = delete;

  void resize(const std::size_t num_threads,
              const std::size_t size_per_thread) {
    m_num_threads     = num_threads;
    m_size_per_thread = size_per_thread;

    pad_to_cache_line(m_size_per_thread);

    std::size_t size_total_new = m_num_threads * m_size_per_thread;

    if (m_size_total < size_total_new) {
      delete[] m_data;
      m_data       = new char[size_total_new];
      m_size_total = size_total_new;
    }
  }

  char *get(std::size_t thread_num) {
    assert(thread_num < m_num_threads);
    if (m_data == nullptr) {
      return nullptr;
    }
    return &m_data[thread_num * m_size_per_thread];
  }

  std::size_t size_per_thread() const noexcept { return m_size_per_thread; }
  std::size_t size_total() const noexcept { return m_size_total; }
};
}  // namespace Impl

namespace Experimental {
class HPX {
 public:
  static constexpr uint32_t impl_default_instance_id() { return 1; }

 private:
  static bool m_hpx_initialized;
  uint32_t m_instance_id = impl_default_instance_id();

#if defined(KOKKOS_ENABLE_HPX_ASYNC_DISPATCH)
  static std::atomic<uint32_t> m_next_instance_id;

 public:
  enum class instance_mode { default_, independent };

 private:
  static uint32_t m_active_parallel_region_count;
  static hpx::spinlock m_active_parallel_region_count_mutex;
  static hpx::condition_variable_any m_active_parallel_region_count_cond;

  struct instance_data {
    instance_data() = default;
    instance_data(hpx::shared_future<void> future) : m_future(future) {}
    Kokkos::Impl::thread_buffer m_buffer;
    hpx::shared_future<void> m_future = hpx::make_ready_future<void>();
    hpx::spinlock m_future_mutex;
  };

  mutable std::shared_ptr<instance_data> m_independent_instance_data;
  static instance_data m_default_instance_data;

  std::reference_wrapper<Kokkos::Impl::thread_buffer> m_buffer;
  std::reference_wrapper<hpx::shared_future<void>> m_future;
  std::reference_wrapper<hpx::spinlock> m_future_mutex;
#else
  static Kokkos::Impl::thread_buffer m_default_buffer;
#endif

 public:
  using execution_space      = HPX;
  using memory_space         = HostSpace;
  using device_type          = Kokkos::Device<execution_space, memory_space>;
  using array_layout         = LayoutRight;
  using size_type            = memory_space::size_type;
  using scratch_memory_space = ScratchMemorySpace<HPX>;

#if defined(KOKKOS_ENABLE_HPX_ASYNC_DISPATCH)
  HPX()
  noexcept
      : m_instance_id(impl_default_instance_id()),
        m_buffer(m_default_instance_data.m_buffer),
        m_future(m_default_instance_data.m_future),
        m_future_mutex(m_default_instance_data.m_future_mutex) {}

  HPX(instance_mode mode)
      : m_instance_id(mode == instance_mode::independent
                          ? m_next_instance_id++
                          : impl_default_instance_id()),
        m_independent_instance_data(mode == instance_mode::independent
                                        ? (new instance_data())
                                        : nullptr),
        m_buffer(mode == instance_mode::independent
                     ? m_independent_instance_data->m_buffer
                     : m_default_instance_data.m_buffer),
        m_future(mode == instance_mode::independent
                     ? m_independent_instance_data->m_future
                     : m_default_instance_data.m_future),
        m_future_mutex(mode == instance_mode::independent
                           ? m_independent_instance_data->m_future_mutex
                           : m_default_instance_data.m_future_mutex) {}

  HPX(hpx::shared_future<void> future)
      : m_instance_id(m_next_instance_id++),

        m_independent_instance_data(new instance_data(future)),
        m_buffer(m_independent_instance_data->m_buffer),
        m_future(m_independent_instance_data->m_future),
        m_future_mutex(m_independent_instance_data->m_future_mutex) {}

  HPX(HPX &&other) = default;
  HPX &operator=(HPX &&other) = default;
  HPX(const HPX &other)       = default;
  HPX &operator=(const HPX &other) = default;
#else
  HPX() noexcept {}
#endif

  void print_configuration(std::ostream &os, bool /*verbose*/ = false) const {
    os << "HPX backend\n";
    os << "HPX Execution Space:\n";
    os << "  KOKKOS_ENABLE_HPX: yes\n";
    os << "\nHPX Runtime Configuration:\n";
  }
  uint32_t impl_instance_id() const noexcept { return m_instance_id; }

#if defined(KOKKOS_ENABLE_HPX_ASYNC_DISPATCH)
  static bool in_parallel(HPX const &instance = HPX()) noexcept {
    return !instance.impl_get_future().is_ready();
  }
#else
  static bool in_parallel(HPX const & = HPX()) noexcept { return false; }
#endif

#if defined(KOKKOS_ENABLE_HPX_ASYNC_DISPATCH)
  static void impl_decrement_active_parallel_region_count() {
    std::unique_lock<hpx::spinlock> l(m_active_parallel_region_count_mutex);
    if (--m_active_parallel_region_count == 0) {
      l.unlock();
      m_active_parallel_region_count_cond.notify_all();
    };
  }

  static void impl_increment_active_parallel_region_count() {
    std::unique_lock<hpx::spinlock> l(m_active_parallel_region_count_mutex);
    ++m_active_parallel_region_count;
  }
#endif

  void fence(
      const std::string &name =
          "Kokkos::Experimental::HPX::fence: Unnamed Instance Fence") const {
    Kokkos::Tools::Experimental::Impl::profile_fence_event<
        Kokkos::Experimental::HPX>(
        name,
        Kokkos::Tools::Experimental::Impl::DirectFenceIDHandle{
            impl_instance_id()},
        [&]() {
#if defined(KOKKOS_ENABLE_HPX_ASYNC_DISPATCH)
          impl_get_future().wait();
          // Reset the future to free variables that may have been captured in
          // parallel regions.
          impl_get_future() = hpx::make_ready_future<void>();
#endif
        });
  }

  static void impl_static_fence(const std::string &name) {
    Kokkos::Tools::Experimental::Impl::profile_fence_event<
        Kokkos::Experimental::HPX>(
        name,
        Kokkos::Tools::Experimental::SpecialSynchronizationCases::
            GlobalDeviceSynchronization,
        [&]() {
#if defined(KOKKOS_ENABLE_HPX_ASYNC_DISPATCH)
          std::unique_lock<hpx::spinlock> l(
              m_active_parallel_region_count_mutex);
          m_active_parallel_region_count_cond.wait(
              l, [&]() { return m_active_parallel_region_count == 0; });
          // Reset the future to free variables that may have been captured in
          // parallel regions (however, we don't have access to futures from
          // instances other than the default instances, they will only be
          // released by fence).
          HPX().impl_get_future() = hpx::make_ready_future<void>();
#endif
        });
  }

  static hpx::execution::parallel_executor impl_get_executor() {
    return hpx::execution::parallel_executor();
  }

  static bool is_asynchronous(HPX const & = HPX()) noexcept {
#if defined(KOKKOS_ENABLE_HPX_ASYNC_DISPATCH)
    return true;
#else
    return false;
#endif
  }

#ifdef KOKKOS_ENABLE_DEPRECATED_CODE_3
  template <typename F>
  KOKKOS_DEPRECATED static void partition_master(
      F const &, int requested_num_partitions = 0, int = 0) {
    if (requested_num_partitions > 1) {
      Kokkos::abort(
          "Kokkos::Experimental::HPX::partition_master: can't partition an "
          "HPX instance\n");
    }
  }
#endif

  static int concurrency();
  static void impl_initialize(InitializationSettings const &);
  static bool impl_is_initialized() noexcept;
  static void impl_finalize();

  static int impl_thread_pool_size() noexcept {
    hpx::runtime *rt = hpx::get_runtime_ptr();
    if (rt == nullptr) {
      return 0;
    } else {
      if (hpx::threads::get_self_ptr() == nullptr) {
        return hpx::resource::get_thread_pool(0).get_os_thread_count();
      } else {
        return hpx::this_thread::get_pool()->get_os_thread_count();
      }
    }
  }

  static int impl_thread_pool_rank() noexcept {
    hpx::runtime *rt = hpx::get_runtime_ptr();
    if (rt == nullptr) {
      return 0;
    } else {
      if (hpx::threads::get_self_ptr() == nullptr) {
        return 0;
      } else {
        return hpx::this_thread::get_pool()->get_pool_index();
      }
    }
  }

  static int impl_thread_pool_size(int depth) {
    if (depth == 0) {
      return impl_thread_pool_size();
    } else {
      return 1;
    }
  }

  static int impl_max_hardware_threads() noexcept {
    return hpx::threads::hardware_concurrency();
  }

  static int impl_hardware_thread_id() noexcept {
    return hpx::get_worker_thread_num();
  }

  Kokkos::Impl::thread_buffer &impl_get_buffer() const noexcept {
#if defined(KOKKOS_ENABLE_HPX_ASYNC_DISPATCH)
    return m_buffer.get();
#else
    return m_default_buffer;
#endif
  }

#if defined(KOKKOS_ENABLE_HPX_ASYNC_DISPATCH)
  hpx::shared_future<void> &impl_get_future() const noexcept {
    return m_future;
  }

  hpx::spinlock &impl_get_future_mutex() const noexcept {
    return m_future_mutex;
  }
#endif

#if defined(KOKKOS_ENABLE_HPX_ASYNC_DISPATCH)
  struct [[nodiscard]] reset_on_exit_parallel {
    HPX const &m_space;
    reset_on_exit_parallel(HPX const &space) : m_space(space) {}
    ~reset_on_exit_parallel() {
      // See [note 1] for an explanation. m_independent_instance_data is
      // marked mutable.
      m_space.m_independent_instance_data.reset();

      HPX::impl_decrement_active_parallel_region_count();
    }
  };

  // This struct is identical to the above except it does not reset the shared
  // data. It does, however, still decrement the parallel region count. It is
  // meant for use in parallel regions which do not capture the execution space
  // instance.
  struct [[nodiscard]] reset_count_on_exit_parallel {
    reset_count_on_exit_parallel() = default;
    ~reset_count_on_exit_parallel() {
      HPX::impl_decrement_active_parallel_region_count();
    }
  };
#else
  struct [[nodiscard]] reset_on_exit_parallel {
    reset_on_exit_parallel(HPX const &) = default;
    ~reset_on_exit_parallel()           = default;
  };

  struct [[nodiscard]] reset_count_on_exit_parallel {
    reset_count_on_exit_parallel()  = default;
    ~reset_count_on_exit_parallel() = default;
  };
#endif

  static constexpr const char *name() noexcept { return "HPX"; }

 private:
  friend bool operator==(HPX const &lhs, HPX const &rhs) {
    return lhs.m_instance_id == rhs.m_instance_id;
  }
  friend bool operator!=(HPX const &lhs, HPX const &rhs) {
    return !(lhs == rhs);
  }
};
}  // namespace Experimental

namespace Tools {
namespace Experimental {
template <>
struct DeviceTypeTraits<Kokkos::Experimental::HPX> {
  static constexpr DeviceType id = DeviceType::HPX;
  static int device_id(const Kokkos::Experimental::HPX &) { return 0; }
};
}  // namespace Experimental
}  // namespace Tools

namespace Impl {

#if defined(KOKKOS_ENABLE_HPX_ASYNC_DISPATCH)
template <typename Closure>
inline void dispatch_execute_task(Closure *closure,
                                  Kokkos::Experimental::HPX const &instance,
                                  bool force_synchronous = false) {
  Kokkos::Experimental::HPX::impl_increment_active_parallel_region_count();

  Closure closure_copy = *closure;

  {
    std::unique_lock<hpx::spinlock> l(instance.impl_get_future_mutex());
    hpx::util::ignore_lock(&instance.impl_get_future_mutex());
    hpx::shared_future<void> &fut = instance.impl_get_future();

    fut = fut.then(hpx::execution::parallel_executor(
                       hpx::threads::thread_schedule_hint(0)),
                   [closure_copy](hpx::shared_future<void> &&) {
                     return closure_copy.execute_task();
                   });
  }

  if (force_synchronous) {
    instance.fence(
        "Kokkos::Experimental::Impl::HPX::dispatch_execute_task: fence due to "
        "forced syncronizations");
  }
}
#else
template <typename Closure>
inline void dispatch_execute_task(Closure *closure,
                                  Kokkos::Experimental::HPX const &,
                                  bool = false) {
  closure->execute_task();
}
#endif
}  // namespace Impl
}  // namespace Kokkos

namespace Kokkos {
namespace Impl {
template <>
struct MemorySpaceAccess<Kokkos::Experimental::HPX::memory_space,
                         Kokkos::Experimental::HPX::scratch_memory_space> {
  enum : bool { assignable = false };
  enum : bool { accessible = true };
  enum : bool { deepcopy = false };
};

}  // namespace Impl
}  // namespace Kokkos

namespace Kokkos {
namespace Experimental {
template <>
class UniqueToken<HPX, UniqueTokenScope::Instance> {
 private:
  using buffer_type = Kokkos::View<uint32_t *, Kokkos::HostSpace>;
  int m_count;
  buffer_type m_buffer_view;
  uint32_t volatile *m_buffer;

 public:
  using execution_space = HPX;
  using size_type       = int;

  /// \brief create object size for concurrency on the given instance
  ///
  /// This object should not be shared between instances
  UniqueToken(execution_space const & = execution_space()) noexcept
      : m_count(execution_space::impl_max_hardware_threads()),
        m_buffer_view(buffer_type()),
        m_buffer(nullptr) {}

  UniqueToken(size_type max_size, execution_space const & = execution_space())
      : m_count(max_size > execution_space::impl_max_hardware_threads()
                    ? execution_space::impl_max_hardware_threads()
                    : max_size),
        m_buffer_view(
            max_size > execution_space::impl_max_hardware_threads()
                ? buffer_type()
                : buffer_type("UniqueToken::m_buffer_view",
                              ::Kokkos::Impl::concurrent_bitset::buffer_bound(
                                  m_count))),
        m_buffer(m_buffer_view.data()) {}

  /// \brief upper bound for acquired values, i.e. 0 <= value < size()
  KOKKOS_INLINE_FUNCTION
  int size() const noexcept { return m_count; }

  /// \brief acquire value such that 0 <= value < size()
  KOKKOS_INLINE_FUNCTION
  int acquire() const noexcept {
    KOKKOS_IF_ON_HOST((
        if (m_buffer == nullptr) {
          return execution_space::impl_hardware_thread_id();
        } else {
          const ::Kokkos::pair<int, int> result =
              ::Kokkos::Impl::concurrent_bitset::acquire_bounded(
                  m_buffer, m_count, ::Kokkos::Impl::clock_tic() % m_count);

          if (result.first < 0) {
            ::Kokkos::abort(
                "UniqueToken<HPX> failure to acquire tokens, no tokens "
                "available");
          }
          return result.first;
        }))

    KOKKOS_IF_ON_DEVICE((return 0;))
  }

  /// \brief release a value acquired by generate
  KOKKOS_INLINE_FUNCTION
  void release(int i) const noexcept {
    KOKKOS_IF_ON_HOST((if (m_buffer != nullptr) {
      ::Kokkos::Impl::concurrent_bitset::release(m_buffer, i);
    }))

    KOKKOS_IF_ON_DEVICE(((void)i;))
  }
};

template <>
class UniqueToken<HPX, UniqueTokenScope::Global> {
 public:
  using execution_space = HPX;
  using size_type       = int;
  UniqueToken(execution_space const & = execution_space()) noexcept {}

  // NOTE: Currently this assumes that there is no oversubscription.
  // hpx::get_num_worker_threads can't be used directly because it may yield
  // it's task (problematic if called after hpx::get_worker_thread_num).
  int size() const noexcept { return HPX::impl_max_hardware_threads(); }
  int acquire() const noexcept { return HPX::impl_hardware_thread_id(); }
  void release(int) const noexcept {}
};
}  // namespace Experimental
}  // namespace Kokkos

namespace Kokkos {
namespace Impl {

struct HPXTeamMember {
 public:
  using execution_space = Kokkos::Experimental::HPX;
  using scratch_memory_space =
      Kokkos::ScratchMemorySpace<Kokkos::Experimental::HPX>;
  using team_handle = HPXTeamMember;

 private:
  scratch_memory_space m_team_shared;

  int m_league_size;
  int m_league_rank;
  int m_team_size;
  int m_team_rank;

 public:
  KOKKOS_INLINE_FUNCTION
  const scratch_memory_space &team_shmem() const {
    return m_team_shared.set_team_thread_mode(0, 1, 0);
  }

  KOKKOS_INLINE_FUNCTION
  const execution_space::scratch_memory_space &team_scratch(const int) const {
    return m_team_shared.set_team_thread_mode(0, 1, 0);
  }

  KOKKOS_INLINE_FUNCTION
  const execution_space::scratch_memory_space &thread_scratch(const int) const {
    return m_team_shared.set_team_thread_mode(0, team_size(), team_rank());
  }

  KOKKOS_INLINE_FUNCTION int league_rank() const noexcept {
    return m_league_rank;
  }

  KOKKOS_INLINE_FUNCTION int league_size() const noexcept {
    return m_league_size;
  }

  KOKKOS_INLINE_FUNCTION int team_rank() const noexcept { return m_team_rank; }
  KOKKOS_INLINE_FUNCTION int team_size() const noexcept { return m_team_size; }

  template <class... Properties>
  constexpr KOKKOS_INLINE_FUNCTION HPXTeamMember(
      const TeamPolicyInternal<Kokkos::Experimental::HPX, Properties...>
          &policy,
      const int team_rank, const int league_rank, void *scratch,
      size_t scratch_size) noexcept
      : m_team_shared(scratch, scratch_size, scratch, scratch_size),
        m_league_size(policy.league_size()),
        m_league_rank(league_rank),
        m_team_size(policy.team_size()),
        m_team_rank(team_rank) {}

  KOKKOS_INLINE_FUNCTION
  void team_barrier() const {}

  template <class ValueType>
  KOKKOS_INLINE_FUNCTION void team_broadcast(ValueType &, const int &) const {}

  template <class Closure, class ValueType>
  KOKKOS_INLINE_FUNCTION void team_broadcast(const Closure &closure,
                                             ValueType &value,
                                             const int &) const {
    closure(value);
  }

  template <class ValueType, class JoinOp>
  KOKKOS_INLINE_FUNCTION ValueType team_reduce(const ValueType &value,
                                               const JoinOp &) const {
    return value;
  }

  template <class ReducerType>
  KOKKOS_INLINE_FUNCTION std::enable_if_t<is_reducer<ReducerType>::value>
  team_reduce(const ReducerType &) const {}

  template <typename Type>
  KOKKOS_INLINE_FUNCTION Type
  team_scan(const Type &value, Type *const global_accum = nullptr) const {
    if (global_accum) {
      Kokkos::atomic_fetch_add(global_accum, value);
    }

    return 0;
  }
};

template <class... Properties>
class TeamPolicyInternal<Kokkos::Experimental::HPX, Properties...>
    : public PolicyTraits<Properties...> {
  int m_league_size;
  int m_team_size;
  std::size_t m_team_scratch_size[2];
  std::size_t m_thread_scratch_size[2];
  int m_chunk_size;

 public:
  using traits = PolicyTraits<Properties...>;

  //! Tag this class as a kokkos execution policy
  using execution_policy = TeamPolicyInternal;

  using member_type = HPXTeamMember;

  //! Execution space of this execution policy:
  using execution_space = Kokkos::Experimental::HPX;

  // NOTE: Max size is 1 for simplicity. In most cases more than 1 is not
  // necessary on CPU. Implement later if there is a need.
  template <class FunctorType>
  inline static int team_size_max(const FunctorType &) {
    return 1;
  }

  template <class FunctorType>
  inline static int team_size_recommended(const FunctorType &) {
    return 1;
  }

  template <class FunctorType>
  inline static int team_size_recommended(const FunctorType &, const int &) {
    return 1;
  }

  template <class FunctorType>
  int team_size_max(const FunctorType &, const ParallelForTag &) const {
    return 1;
  }

  template <class FunctorType>
  int team_size_max(const FunctorType &, const ParallelReduceTag &) const {
    return 1;
  }

  template <class FunctorType, class ReducerType>
  int team_size_max(const FunctorType &, const ReducerType &,
                    const ParallelReduceTag &) const {
    return 1;
  }

  template <class FunctorType>
  int team_size_recommended(const FunctorType &, const ParallelForTag &) const {
    return 1;
  }

  template <class FunctorType>
  int team_size_recommended(const FunctorType &,
                            const ParallelReduceTag &) const {
    return 1;
  }

  template <class FunctorType, class ReducerType>
  int team_size_recommended(const FunctorType &, const ReducerType &,
                            const ParallelReduceTag &) const {
    return 1;
  }

  static int vector_length_max() { return 1; }

  inline int impl_vector_length() noexcept { return 1; }
  inline bool impl_auto_team_size() noexcept { return false; }
  inline bool impl_auto_vector_length() noexcept { return false; }
  inline void impl_set_vector_length(int) noexcept {}
  inline void impl_set_team_size(int) noexcept {}

 private:
  inline void init(const int league_size_request, const int team_size_request) {
    m_league_size           = league_size_request;
    const int max_team_size = 1;  // TODO: Can't use team_size_max(...) because
                                  // it requires a functor as argument.
    m_team_size =
        team_size_request > max_team_size ? max_team_size : team_size_request;

    if (m_chunk_size > 0) {
      if (!Impl::is_integral_power_of_two(m_chunk_size))
        Kokkos::abort("TeamPolicy blocking granularity must be power of two");
    } else {
      int new_chunk_size = 1;
      while (new_chunk_size * 4 * Kokkos::Experimental::HPX::concurrency() <
             m_league_size) {
        new_chunk_size *= 2;
      }

      if (new_chunk_size < 128) {
        new_chunk_size = 1;
        while ((new_chunk_size * Kokkos::Experimental::HPX::concurrency() <
                m_league_size) &&
               (new_chunk_size < 128))
          new_chunk_size *= 2;
      }

      m_chunk_size = new_chunk_size;
    }
  }

 public:
  inline int team_size() const { return m_team_size; }
  inline int league_size() const { return m_league_size; }

  size_t scratch_size(const int &level, int team_size_ = -1) const {
    if (team_size_ < 0) {
      team_size_ = m_team_size;
    }
    return m_team_scratch_size[level] +
           team_size_ * m_thread_scratch_size[level];
  }

  inline static int scratch_size_max(int level) {
    return (level == 0 ? 1024 * 32 :  // Roughly L1 size
                20 * 1024 * 1024);    // Limit to keep compatibility with CUDA
  }

 public:
  template <class ExecSpace, class... OtherProperties>
  friend class TeamPolicyInternal;

  const typename traits::execution_space &space() const {
    static typename traits::execution_space m_space;
    return m_space;
  }

  template <class... OtherProperties>
  TeamPolicyInternal(const TeamPolicyInternal<Kokkos::Experimental::HPX,
                                              OtherProperties...> &p) {
    m_league_size            = p.m_league_size;
    m_team_size              = p.m_team_size;
    m_team_scratch_size[0]   = p.m_team_scratch_size[0];
    m_thread_scratch_size[0] = p.m_thread_scratch_size[0];
    m_team_scratch_size[1]   = p.m_team_scratch_size[1];
    m_thread_scratch_size[1] = p.m_thread_scratch_size[1];
    m_chunk_size             = p.m_chunk_size;
  }

  TeamPolicyInternal(const typename traits::execution_space &,
                     int league_size_request, int team_size_request,
                     int /* vector_length_request */ = 1)
      : m_team_scratch_size{0, 0},
        m_thread_scratch_size{0, 0},
        m_chunk_size(0) {
    init(league_size_request, team_size_request);
  }

  TeamPolicyInternal(const typename traits::execution_space &,
                     int league_size_request, const Kokkos::AUTO_t &,
                     int /* vector_length_request */ = 1)
      : m_team_scratch_size{0, 0},
        m_thread_scratch_size{0, 0},
        m_chunk_size(0) {
    init(league_size_request, 1);
  }

  TeamPolicyInternal(const typename traits::execution_space &,
                     int league_size_request,
                     const Kokkos::AUTO_t &, /* team_size_request */
                     const Kokkos::AUTO_t & /* vector_length_request */)
      : m_team_scratch_size{0, 0},
        m_thread_scratch_size{0, 0},
        m_chunk_size(0) {
    init(league_size_request, 1);
  }

  TeamPolicyInternal(const typename traits::execution_space &,
                     int league_size_request, int team_size_request,
                     const Kokkos::AUTO_t & /* vector_length_request */
                     )
      : m_team_scratch_size{0, 0},
        m_thread_scratch_size{0, 0},
        m_chunk_size(0) {
    init(league_size_request, team_size_request);
  }

  TeamPolicyInternal(int league_size_request,
                     const Kokkos::AUTO_t &, /* team_size_request */
                     const Kokkos::AUTO_t & /* vector_length_request */)
      : m_team_scratch_size{0, 0},
        m_thread_scratch_size{0, 0},
        m_chunk_size(0) {
    init(league_size_request, 1);
  }

  TeamPolicyInternal(int league_size_request, int team_size_request,
                     const Kokkos::AUTO_t & /* vector_length_request */
                     )
      : m_team_scratch_size{0, 0},
        m_thread_scratch_size{0, 0},
        m_chunk_size(0) {
    init(league_size_request, team_size_request);
  }

  TeamPolicyInternal(int league_size_request, int team_size_request,
                     int /* vector_length_request */ = 1)
      : m_team_scratch_size{0, 0},
        m_thread_scratch_size{0, 0},
        m_chunk_size(0) {
    init(league_size_request, team_size_request);
  }

  TeamPolicyInternal(int league_size_request, const Kokkos::AUTO_t &,
                     int /* vector_length_request */ = 1)
      : m_team_scratch_size{0, 0},
        m_thread_scratch_size{0, 0},
        m_chunk_size(0) {
    init(league_size_request, 1);
  }

  inline int chunk_size() const { return m_chunk_size; }

  inline TeamPolicyInternal &set_chunk_size(
      typename traits::index_type chunk_size_) {
    m_chunk_size = chunk_size_;
    return *this;
  }

  inline TeamPolicyInternal &set_scratch_size(const int &level,
                                              const PerTeamValue &per_team) {
    m_team_scratch_size[level] = per_team.value;
    return *this;
  }

  inline TeamPolicyInternal &set_scratch_size(
      const int &level, const PerThreadValue &per_thread) {
    m_thread_scratch_size[level] = per_thread.value;
    return *this;
  }

  inline TeamPolicyInternal &set_scratch_size(
      const int &level, const PerTeamValue &per_team,
      const PerThreadValue &per_thread) {
    m_team_scratch_size[level]   = per_team.value;
    m_thread_scratch_size[level] = per_thread.value;
    return *this;
  }
};
}  // namespace Impl
}  // namespace Kokkos

namespace Kokkos {
namespace Impl {

template <typename Policy>
typename Policy::member_type get_hpx_adjusted_chunk_size(Policy const &policy) {
  const int concurrency = Kokkos::Experimental::HPX::concurrency();
  const typename Policy::member_type n        = policy.end() - policy.begin();
  typename Policy::member_type new_chunk_size = policy.chunk_size();

  while (n >= 4 * concurrency * new_chunk_size) {
    new_chunk_size *= 2;
  }

  return new_chunk_size;
}

template <class FunctorType, class... Traits>
class ParallelFor<FunctorType, Kokkos::RangePolicy<Traits...>,
                  Kokkos::Experimental::HPX> {
 private:
  using Policy    = Kokkos::RangePolicy<Traits...>;
  using WorkTag   = typename Policy::work_tag;
  using WorkRange = typename Policy::WorkRange;
  using Member    = typename Policy::member_type;

  const FunctorType m_functor;
  const Policy m_policy;

  template <class TagType>
  static std::enable_if_t<std::is_void<TagType>::value> execute_functor(
      const FunctorType &functor, const Member i) {
    functor(i);
  }

  template <class TagType>
  static std::enable_if_t<!std::is_void<TagType>::value> execute_functor(
      const FunctorType &functor, const Member i) {
    const TagType t{};
    functor(t, i);
  }

  template <class TagType>
  static std::enable_if_t<std::is_void<TagType>::value> execute_functor_range(
      const FunctorType &functor, const Member i_begin, const Member i_end) {
    for (Member i = i_begin; i < i_end; ++i) {
      functor(i);
    }
  }

  template <class TagType>
  static std::enable_if_t<!std::is_void<TagType>::value> execute_functor_range(
      const FunctorType &functor, const Member i_begin, const Member i_end) {
    const TagType t{};
    for (Member i = i_begin; i < i_end; ++i) {
      functor(t, i);
    }
  }

 public:
  void execute() const {
    Kokkos::Impl::dispatch_execute_task(this, m_policy.space());
  }

  void execute_task() const {
    // See [note 1] for an explanation.
    Kokkos::Experimental::HPX::reset_on_exit_parallel reset_on_exit(
        m_policy.space());

    auto exec = Kokkos::Experimental::HPX::impl_get_executor();

    using hpx::execution::par;
    using hpx::execution::static_chunk_size;

#if KOKKOS_HPX_IMPLEMENTATION == 0
    using hpx::for_loop;

    for_loop(par.on(exec).with(static_chunk_size(m_policy.chunk_size())),
             m_policy.begin(), m_policy.end(), [this](const Member i) {
               execute_functor<WorkTag>(m_functor, i);
             });

#elif KOKKOS_HPX_IMPLEMENTATION == 1
    using hpx::for_loop_strided;

    const Member chunk_size = get_hpx_adjusted_chunk_size(m_policy);

    for_loop_strided(
        par.on(exec), m_policy.begin(), m_policy.end(), chunk_size,
        [this, chunk_size](const Member i_begin) {
          const Member i_end = (std::min)(i_begin + chunk_size, m_policy.end());
          execute_functor_range<WorkTag>(m_functor, i_begin, i_end);
        });
#endif
  }

  inline ParallelFor(const FunctorType &arg_functor, Policy arg_policy)
      : m_functor(arg_functor), m_policy(arg_policy) {}
};

template <class FunctorType, class... Traits>
class ParallelFor<FunctorType, Kokkos::MDRangePolicy<Traits...>,
                  Kokkos::Experimental::HPX> {
 private:
  using MDRangePolicy = Kokkos::MDRangePolicy<Traits...>;
  using Policy        = typename MDRangePolicy::impl_range_policy;
  using WorkTag       = typename MDRangePolicy::work_tag;
  using WorkRange     = typename Policy::WorkRange;
  using Member        = typename Policy::member_type;
  using iterate_type =
      typename Kokkos::Impl::HostIterateTile<MDRangePolicy, FunctorType,
                                             WorkTag, void>;

  const iterate_type m_iter;
  const Policy m_policy;

 public:
  void execute() const { dispatch_execute_task(this, m_iter.m_rp.space()); }

  inline void execute_task() const {
    // See [note 1] for an explanation.
    Kokkos::Experimental::HPX::reset_on_exit_parallel reset_on_exit(
        m_iter.m_rp.space());

    auto exec = Kokkos::Experimental::HPX::impl_get_executor();

    using hpx::execution::par;
    using hpx::execution::static_chunk_size;

#if KOKKOS_HPX_IMPLEMENTATION == 0
    using hpx::for_loop;

    for_loop(par.on(exec).with(
                 static_chunk_size(get_hpx_adjusted_chunk_size(m_policy))),
             m_policy.begin(), m_policy.end(),
             [this](const Member i) { iterate_type(i); });

#elif KOKKOS_HPX_IMPLEMENTATION == 1
    using hpx::for_loop_strided;

    const Member chunk_size = get_hpx_adjusted_chunk_size(m_policy);

    for_loop_strided(par.on(exec), m_policy.begin(), m_policy.end(), chunk_size,
                     [this, chunk_size](const Member i_begin) {
                       const Member i_end =
                           (std::min)(i_begin + chunk_size, m_policy.end());
                       for (Member i = i_begin; i < i_end; ++i) {
                         m_iter(i);
                       }
                     });
#endif
  }

  inline ParallelFor(const FunctorType &arg_functor, MDRangePolicy arg_policy)
      : m_iter(arg_policy, arg_functor),
        m_policy(Policy(0, arg_policy.m_num_tiles).set_chunk_size(1)) {}
  template <typename Policy, typename Functor>
  static int max_tile_size_product(const Policy &, const Functor &) {
    /**
     * 1024 here is just our guess for a reasonable max tile size,
     * it isn't a hardware constraint. If people see a use for larger
     * tile size products, we're happy to change this.
     */
    return 1024;
  }
};
}  // namespace Impl
}  // namespace Kokkos

namespace Kokkos {
namespace Impl {
template <class FunctorType, class ReducerType, class... Traits>
class ParallelReduce<FunctorType, Kokkos::RangePolicy<Traits...>, ReducerType,
                     Kokkos::Experimental::HPX> {
 private:
  using Policy    = Kokkos::RangePolicy<Traits...>;
  using WorkTag   = typename Policy::work_tag;
  using WorkRange = typename Policy::WorkRange;
  using Member    = typename Policy::member_type;
  using ReducerConditional =
      Kokkos::Impl::if_c<std::is_same<InvalidType, ReducerType>::value,
                         FunctorType, ReducerType>;
  using ReducerTypeFwd = typename ReducerConditional::type;
  using Analysis =
      FunctorAnalysis<FunctorPatternInterface::REDUCE, Policy, ReducerTypeFwd>;
  using value_type     = typename Analysis::value_type;
  using pointer_type   = typename Analysis::pointer_type;
  using reference_type = typename Analysis::reference_type;

  const FunctorType m_functor;
  const Policy m_policy;
  const ReducerType m_reducer;
  const pointer_type m_result_ptr;

  bool m_force_synchronous;

  template <class TagType>
  inline static std::enable_if_t<std::is_void<TagType>::value> execute_functor(
      const FunctorType &functor, const Member i, reference_type update) {
    functor(i, update);
  }

  template <class TagType>
  inline static std::enable_if_t<!std::is_void<TagType>::value> execute_functor(
      const FunctorType &functor, const Member i, reference_type update) {
    const TagType t{};
    functor(t, i, update);
  }

  template <class TagType>
  inline std::enable_if_t<std::is_void<TagType>::value> execute_functor_range(
      reference_type update, const Member i_begin, const Member i_end) const {
    for (Member i = i_begin; i < i_end; ++i) {
      m_functor(i, update);
    }
  }

  template <class TagType>
  inline std::enable_if_t<!std::is_void<TagType>::value> execute_functor_range(
      reference_type update, const Member i_begin, const Member i_end) const {
    const TagType t{};

    for (Member i = i_begin; i < i_end; ++i) {
      m_functor(t, i, update);
    }
  }

  class value_type_wrapper {
   private:
    std::size_t m_value_size;
    char *m_value_buffer;

   public:
    value_type_wrapper() : m_value_size(0), m_value_buffer(nullptr) {}

    value_type_wrapper(const std::size_t value_size)
        : m_value_size(value_size), m_value_buffer(new char[m_value_size]) {}

    value_type_wrapper(const value_type_wrapper &other)
        : m_value_size(0), m_value_buffer(nullptr) {
      if (this != &other) {
        m_value_buffer = new char[other.m_value_size];
        m_value_size   = other.m_value_size;

        std::copy(other.m_value_buffer, other.m_value_buffer + m_value_size,
                  m_value_buffer);
      }
    }

    ~value_type_wrapper() { delete[] m_value_buffer; }

    value_type_wrapper(value_type_wrapper &&other)
        : m_value_size(0), m_value_buffer(nullptr) {
      if (this != &other) {
        m_value_buffer = other.m_value_buffer;
        m_value_size   = other.m_value_size;

        other.m_value_buffer = nullptr;
        other.m_value_size   = 0;
      }
    }

    value_type_wrapper &operator=(const value_type_wrapper &other) {
      if (this != &other) {
        delete[] m_value_buffer;
        m_value_buffer = new char[other.m_value_size];
        m_value_size   = other.m_value_size;

        std::copy(other.m_value_buffer, other.m_value_buffer + m_value_size,
                  m_value_buffer);
      }

      return *this;
    }

    value_type_wrapper &operator=(value_type_wrapper &&other) {
      if (this != &other) {
        delete[] m_value_buffer;
        m_value_buffer = other.m_value_buffer;
        m_value_size   = other.m_value_size;

        other.m_value_buffer = nullptr;
        other.m_value_size   = 0;
      }

      return *this;
    }

    pointer_type pointer() const {
      return reinterpret_cast<pointer_type>(m_value_buffer);
    }

    reference_type reference() const {
      return Analysis::Reducer::reference(
          reinterpret_cast<pointer_type>(m_value_buffer));
    }
  };

 public:
  void execute() const {
    if (m_policy.end() <= m_policy.begin()) {
      if (m_result_ptr) {
        typename Analysis::Reducer final_reducer(
            &ReducerConditional::select(m_functor, m_reducer));

        final_reducer.init(m_result_ptr);
        final_reducer.final(m_result_ptr);
      }
      return;
    }
    dispatch_execute_task(this, m_policy.space(), m_force_synchronous);
  }

  inline void execute_task() const {
    // See [note 1] for an explanation.
    Kokkos::Experimental::HPX::reset_on_exit_parallel reset_on_exit(
        m_policy.space());

    typename Analysis::Reducer final_reducer(
        &ReducerConditional::select(m_functor, m_reducer));

    const std::size_t value_size =
        Analysis::value_size(ReducerConditional::select(m_functor, m_reducer));

    auto exec = Kokkos::Experimental::HPX::impl_get_executor();

    using hpx::for_loop;
    using hpx::execution::par;
    using hpx::execution::static_chunk_size;

#if KOKKOS_HPX_IMPLEMENTATION == 0
    // NOTE: This version makes the most use of HPX functionality, but
    // requires the struct value_type_wrapper to handle different
    // reference_types. It is also significantly slower than the version
    // below due to not reusing the buffer used by other functions.
    using hpx::parallel::reduction;

    value_type_wrapper final_value(value_size);
    value_type_wrapper identity(value_size);

    final_reducer.init(final_value.pointer());
    final_reducer.init(identity.pointer());

    for_loop(par.on(exec).with(
                 static_chunk_size(get_hpx_adjusted_chunk_size(m_policy))),
             m_policy.begin(), m_policy.end(),
             reduction(final_value, identity,
                       [final_reducer](
                           value_type_wrapper &a,
                           value_type_wrapper &b) -> value_type_wrapper & {
                         final_reducer.join(a.pointer(), b.pointer());
                         return a;
                       }),
             [this](Member i, value_type_wrapper &update) {
               execute_functor<WorkTag>(m_functor, i, update.reference());
             });

    pointer_type final_value_ptr = final_value.pointer();

#elif KOKKOS_HPX_IMPLEMENTATION == 1
    using hpx::for_loop_strided;

    const int num_worker_threads = Kokkos::Experimental::HPX::concurrency();

    thread_buffer &buffer = m_policy.space().impl_get_buffer();
    buffer.resize(num_worker_threads, value_size);

    for_loop(
        par.on(exec).with(static_chunk_size(1)), 0, num_worker_threads,
        [&buffer, final_reducer ](const int t) noexcept {
          final_reducer.init(reinterpret_cast<pointer_type>(buffer.get(t)));
        });

    const Member chunk_size = get_hpx_adjusted_chunk_size(m_policy);

    for_loop_strided(
        par.on(exec), m_policy.begin(), m_policy.end(), chunk_size,
        [this, &buffer, chunk_size](const Member i_begin) {
          reference_type update = Analysis::Reducer::reference(
              reinterpret_cast<pointer_type>(buffer.get(
                  Kokkos::Experimental::HPX::impl_hardware_thread_id())));
          const Member i_end = (std::min)(i_begin + chunk_size, m_policy.end());
          execute_functor_range<WorkTag>(update, i_begin, i_end);
        });

    for (int i = 1; i < num_worker_threads; ++i) {
      final_reducer.join(reinterpret_cast<pointer_type>(buffer.get(0)),
                         reinterpret_cast<pointer_type>(buffer.get(i)));
    }

    pointer_type final_value_ptr =
        reinterpret_cast<pointer_type>(buffer.get(0));
#endif

    final_reducer.final(final_value_ptr);

    if (m_result_ptr != nullptr) {
      const int n = Analysis::value_count(
          ReducerConditional::select(m_functor, m_reducer));

      for (int j = 0; j < n; ++j) {
        m_result_ptr[j] = final_value_ptr[j];
      }
    }
  }

  template <class ViewType>
  inline ParallelReduce(
      const FunctorType &arg_functor, Policy arg_policy,
      const ViewType &arg_view,
      std::enable_if_t<Kokkos::is_view<ViewType>::value &&
                           !Kokkos::is_reducer<ReducerType>::value,
                       void *> = nullptr)
      : m_functor(arg_functor),
        m_policy(arg_policy),
        m_reducer(InvalidType()),
        m_result_ptr(arg_view.data()),
        m_force_synchronous(!arg_view.impl_track().has_record()) {}

  inline ParallelReduce(const FunctorType &arg_functor, Policy arg_policy,
                        const ReducerType &reducer)
      : m_functor(arg_functor),
        m_policy(arg_policy),
        m_reducer(reducer),
        m_result_ptr(reducer.view().data()),
        m_force_synchronous(!reducer.view().impl_track().has_record()) {}
};

template <class FunctorType, class ReducerType, class... Traits>
class ParallelReduce<FunctorType, Kokkos::MDRangePolicy<Traits...>, ReducerType,
                     Kokkos::Experimental::HPX> {
 private:
  using MDRangePolicy = Kokkos::MDRangePolicy<Traits...>;
  using Policy        = typename MDRangePolicy::impl_range_policy;
  using WorkTag       = typename MDRangePolicy::work_tag;
  using WorkRange     = typename Policy::WorkRange;
  using Member        = typename Policy::member_type;
  using ReducerConditional =
      Kokkos::Impl::if_c<std::is_same<InvalidType, ReducerType>::value,
                         FunctorType, ReducerType>;
  using ReducerTypeFwd = typename ReducerConditional::type;
  using Analysis       = FunctorAnalysis<FunctorPatternInterface::REDUCE,
                                   MDRangePolicy, ReducerTypeFwd>;

  using pointer_type   = typename Analysis::pointer_type;
  using value_type     = typename Analysis::value_type;
  using reference_type = typename Analysis::reference_type;
  using iterate_type =
      typename Kokkos::Impl::HostIterateTile<MDRangePolicy, FunctorType,
                                             WorkTag, reference_type>;

  const iterate_type m_iter;
  const Policy m_policy;
  const ReducerType m_reducer;
  const pointer_type m_result_ptr;

  bool m_force_synchronous;

 public:
  void execute() const {
    dispatch_execute_task(this, m_iter.m_rp.space(), m_force_synchronous);
  }

  inline void execute_task() const {
    // See [note 1] for an explanation.
    Kokkos::Experimental::HPX::reset_on_exit_parallel reset_on_exit(
        m_iter.m_rp.space());

    const int num_worker_threads = Kokkos::Experimental::HPX::concurrency();
    const std::size_t value_size = Analysis::value_size(
        ReducerConditional::select(m_iter.m_func, m_reducer));

    thread_buffer &buffer = m_iter.m_rp.space().impl_get_buffer();
    buffer.resize(num_worker_threads, value_size);

    using hpx::for_loop;
    using hpx::execution::par;
    using hpx::execution::static_chunk_size;

    auto exec = Kokkos::Experimental::HPX::impl_get_executor();

    typename Analysis::Reducer final_reducer(
        &ReducerConditional::select(m_iter.m_func, m_reducer));

#if KOKKOS_HPX_IMPLEMENTATION == 0

    for_loop(
        par.on(exec).with(static_chunk_size(1)), 0, num_worker_threads,
        [&buffer, final_reducer](std::size_t t) {
          final_reducer.init(reinterpret_cast<pointer_type>(buffer.get(t)));
        });

    for_loop(par.on(exec).with(
                 static_chunk_size(get_hpx_adjusted_chunk_size(m_policy))),
             m_policy.begin(), m_policy.end(), [this, &buffer](const Member i) {
               reference_type update = Analysis::Reducer::reference(
                   reinterpret_cast<pointer_type>(buffer.get(
                       Kokkos::Experimental::HPX::impl_hardware_thread_id())));
               m_iter(i, update);
             });

#elif KOKKOS_HPX_IMPLEMENTATION == 1
    using hpx::for_loop_strided;

    for_loop(
        par.on(exec).with(static_chunk_size(1)), std::size_t(0),
        num_worker_threads, [&buffer, final_reducer](const std::size_t t) {
          final_reducer.init(reinterpret_cast<pointer_type>(buffer.get(t)));
        });

    const Member chunk_size = get_hpx_adjusted_chunk_size(m_policy);

    for_loop_strided(
        par.on(exec), m_policy.begin(), m_policy.end(), chunk_size,
        [this, &buffer, chunk_size](const Member i_begin) {
          reference_type update = Analysis::Reducer::reference(
              reinterpret_cast<pointer_type>(buffer.get(
                  Kokkos::Experimental::HPX::impl_hardware_thread_id())));
          const Member i_end = (std::min)(i_begin + chunk_size, m_policy.end());

          for (Member i = i_begin; i < i_end; ++i) {
            m_iter(i, update);
          }
        });
#endif

    for (int i = 1; i < num_worker_threads; ++i) {
      final_reducer.join(reinterpret_cast<pointer_type>(buffer.get(0)),
                         reinterpret_cast<pointer_type>(buffer.get(i)));
    }

    final_reducer.final(reinterpret_cast<pointer_type>(buffer.get(0)));

    if (m_result_ptr != nullptr) {
      const int n = Analysis::value_count(
          ReducerConditional::select(m_iter.m_func, m_reducer));

      for (int j = 0; j < n; ++j) {
        m_result_ptr[j] = reinterpret_cast<pointer_type>(buffer.get(0))[j];
      }
    }
  }

  template <class ViewType>
  inline ParallelReduce(
      const FunctorType &arg_functor, MDRangePolicy arg_policy,
      const ViewType &arg_view,
      std::enable_if_t<Kokkos::is_view<ViewType>::value &&
                           !Kokkos::is_reducer<ReducerType>::value,
                       void *> = nullptr)
      : m_iter(arg_policy, arg_functor),
        m_policy(Policy(0, arg_policy.m_num_tiles).set_chunk_size(1)),
        m_reducer(InvalidType()),
        m_result_ptr(arg_view.data()),
        m_force_synchronous(!arg_view.impl_track().has_record()) {}

  inline ParallelReduce(const FunctorType &arg_functor,
                        MDRangePolicy arg_policy, const ReducerType &reducer)
      : m_iter(arg_policy, arg_functor),
        m_policy(Policy(0, arg_policy.m_num_tiles).set_chunk_size(1)),
        m_reducer(reducer),
        m_result_ptr(reducer.view().data()),
        m_force_synchronous(!reducer.view().impl_track().has_record()) {}
  template <typename Policy, typename Functor>
  static int max_tile_size_product(const Policy &, const Functor &) {
    /**
     * 1024 here is just our guess for a reasonable max tile size,
     * it isn't a hardware constraint. If people see a use for larger
     * tile size products, we're happy to change this.
     */
    return 1024;
  }
};
}  // namespace Impl
}  // namespace Kokkos

namespace Kokkos {
namespace Impl {

template <class FunctorType, class... Traits>
class ParallelScan<FunctorType, Kokkos::RangePolicy<Traits...>,
                   Kokkos::Experimental::HPX> {
 private:
  using Policy    = Kokkos::RangePolicy<Traits...>;
  using WorkTag   = typename Policy::work_tag;
  using WorkRange = typename Policy::WorkRange;
  using Member    = typename Policy::member_type;
  using Analysis =
      FunctorAnalysis<FunctorPatternInterface::SCAN, Policy, FunctorType>;
  using pointer_type   = typename Analysis::pointer_type;
  using reference_type = typename Analysis::reference_type;
  using value_type     = typename Analysis::value_type;

  const FunctorType m_functor;
  const Policy m_policy;

  template <class TagType>
  inline static std::enable_if_t<std::is_void<TagType>::value>
  execute_functor_range(const FunctorType &functor, const Member i_begin,
                        const Member i_end, reference_type update,
                        const bool final) {
    for (Member i = i_begin; i < i_end; ++i) {
      functor(i, update, final);
    }
  }

  template <class TagType>
  inline static std::enable_if_t<!std::is_void<TagType>::value>
  execute_functor_range(const FunctorType &functor, const Member i_begin,
                        const Member i_end, reference_type update,
                        const bool final) {
    const TagType t{};
    for (Member i = i_begin; i < i_end; ++i) {
      functor(t, i, update, final);
    }
  }

 public:
  void execute() const { dispatch_execute_task(this, m_policy.space()); }

  inline void execute_task() const {
    // See [note 1] for an explanation.
    Kokkos::Experimental::HPX::reset_on_exit_parallel reset_on_exit(
        m_policy.space());

    const int num_worker_threads = Kokkos::Experimental::HPX::concurrency();
    const int value_count        = Analysis::value_count(m_functor);
    const std::size_t value_size = Analysis::value_size(m_functor);

    thread_buffer &buffer = m_policy.space().impl_get_buffer();
    buffer.resize(num_worker_threads, 2 * value_size);

    using hpx::barrier;
    using hpx::for_loop;
    using hpx::execution::par;
    using hpx::execution::static_chunk_size;

    barrier<> bar(num_worker_threads);
    auto exec = Kokkos::Experimental::HPX::impl_get_executor();

    typename Analysis::Reducer final_reducer(&m_functor);

    for_loop(
        par.on(exec).with(static_chunk_size(1)), 0, num_worker_threads,
        [this, &bar, &buffer, num_worker_threads, value_count, value_size,
         final_reducer](int t) {
          reference_type update_sum =
              final_reducer.init(reinterpret_cast<pointer_type>(buffer.get(t)));

          const WorkRange range(m_policy, t, num_worker_threads);
          execute_functor_range<WorkTag>(m_functor, range.begin(), range.end(),
                                         update_sum, false);

          bar.arrive_and_wait();

          if (t == 0) {
            final_reducer.init(
                reinterpret_cast<pointer_type>(buffer.get(0) + value_size));

            for (int i = 1; i < num_worker_threads; ++i) {
              pointer_type ptr_1_prev =
                  reinterpret_cast<pointer_type>(buffer.get(i - 1));
              pointer_type ptr_2_prev = reinterpret_cast<pointer_type>(
                  buffer.get(i - 1) + value_size);
              pointer_type ptr_2 =
                  reinterpret_cast<pointer_type>(buffer.get(i) + value_size);

              for (int j = 0; j < value_count; ++j) {
                ptr_2[j] = ptr_2_prev[j];
              }

              final_reducer.join(ptr_2, ptr_1_prev);
            }
          }

          bar.arrive_and_wait();

          reference_type update_base = Analysis::Reducer::reference(
              reinterpret_cast<pointer_type>(buffer.get(t) + value_size));

          execute_functor_range<WorkTag>(m_functor, range.begin(), range.end(),
                                         update_base, true);
        });
  }

  inline ParallelScan(const FunctorType &arg_functor, const Policy &arg_policy)
      : m_functor(arg_functor), m_policy(arg_policy) {}
};

template <class FunctorType, class ReturnType, class... Traits>
class ParallelScanWithTotal<FunctorType, Kokkos::RangePolicy<Traits...>,
                            ReturnType, Kokkos::Experimental::HPX> {
 private:
  using Policy    = Kokkos::RangePolicy<Traits...>;
  using WorkTag   = typename Policy::work_tag;
  using WorkRange = typename Policy::WorkRange;
  using Member    = typename Policy::member_type;
  using Analysis =
      FunctorAnalysis<FunctorPatternInterface::SCAN, Policy, FunctorType>;
  using pointer_type   = typename Analysis::pointer_type;
  using reference_type = typename Analysis::reference_type;
  using value_type     = typename Analysis::value_type;

  const FunctorType m_functor;
  const Policy m_policy;
  pointer_type m_result_ptr;

  template <class TagType>
  inline static std::enable_if_t<std::is_void<TagType>::value>
  execute_functor_range(const FunctorType &functor, const Member i_begin,
                        const Member i_end, reference_type update,
                        const bool final) {
    for (Member i = i_begin; i < i_end; ++i) {
      functor(i, update, final);
    }
  }

  template <class TagType>
  inline static std::enable_if_t<!std::is_void<TagType>::value>
  execute_functor_range(const FunctorType &functor, const Member i_begin,
                        const Member i_end, reference_type update,
                        const bool final) {
    const TagType t{};
    for (Member i = i_begin; i < i_end; ++i) {
      functor(t, i, update, final);
    }
  }

 public:
  void execute() const { dispatch_execute_task(this, m_policy.space()); }

  inline void execute_task() const {
    // See [note 1] for an explanation.
    Kokkos::Experimental::HPX::reset_on_exit_parallel reset_on_exit(
        m_policy.space());

    const int num_worker_threads = Kokkos::Experimental::HPX::concurrency();
    const int value_count        = Analysis::value_count(m_functor);
    const std::size_t value_size = Analysis::value_size(m_functor);

    thread_buffer &buffer = m_policy.space().impl_get_buffer();
    buffer.resize(num_worker_threads, 2 * value_size);

    using hpx::barrier;
    using hpx::for_loop;
    using hpx::execution::par;
    using hpx::execution::static_chunk_size;

    barrier<> bar(num_worker_threads);
    auto exec = Kokkos::Experimental::HPX::impl_get_executor();

    typename Analysis::Reducer final_reducer(&m_functor);

    for_loop(
        par.on(exec).with(static_chunk_size(1)), 0, num_worker_threads,
        [this, &bar, &buffer, num_worker_threads, value_count, value_size,
         final_reducer](int t) {
          reference_type update_sum =
              final_reducer.init(reinterpret_cast<pointer_type>(buffer.get(t)));

          const WorkRange range(m_policy, t, num_worker_threads);
          execute_functor_range<WorkTag>(m_functor, range.begin(), range.end(),
                                         update_sum, false);

          bar.arrive_and_wait();

          if (t == 0) {
            final_reducer.init(
                reinterpret_cast<pointer_type>(buffer.get(0) + value_size));

            for (int i = 1; i < num_worker_threads; ++i) {
              pointer_type ptr_1_prev =
                  reinterpret_cast<pointer_type>(buffer.get(i - 1));
              pointer_type ptr_2_prev = reinterpret_cast<pointer_type>(
                  buffer.get(i - 1) + value_size);
              pointer_type ptr_2 =
                  reinterpret_cast<pointer_type>(buffer.get(i) + value_size);

              for (int j = 0; j < value_count; ++j) {
                ptr_2[j] = ptr_2_prev[j];
              }

              final_reducer.join(ptr_2, ptr_1_prev);
            }
          }

          bar.arrive_and_wait();

          reference_type update_base = Analysis::Reducer::reference(
              reinterpret_cast<pointer_type>(buffer.get(t) + value_size));

          execute_functor_range<WorkTag>(m_functor, range.begin(), range.end(),
                                         update_base, true);

          if (t == num_worker_threads - 1) {
            *m_result_ptr = update_base;
          }
        });
  }

  template <class ViewType>
  ParallelScanWithTotal(const FunctorType &arg_functor,
                        const Policy &arg_policy,
                        const ViewType &arg_result_view)
      : m_functor(arg_functor),
        m_policy(arg_policy),
        m_result_ptr(arg_result_view.data()) {
    static_assert(
        Kokkos::Impl::MemorySpaceAccess<typename ViewType::memory_space,
                                        Kokkos::HostSpace>::accessible,
        "Kokkos::HPX parallel_scan result must be host-accessible!");
  }
};
}  // namespace Impl
}  // namespace Kokkos

namespace Kokkos {
namespace Impl {
template <class FunctorType, class... Properties>
class ParallelFor<FunctorType, Kokkos::TeamPolicy<Properties...>,
                  Kokkos::Experimental::HPX> {
 private:
  using Policy  = TeamPolicyInternal<Kokkos::Experimental::HPX, Properties...>;
  using WorkTag = typename Policy::work_tag;
  using Member  = typename Policy::member_type;
  using memory_space = Kokkos::HostSpace;

  const FunctorType m_functor;
  const Policy m_policy;
  const int m_league;
  const std::size_t m_shared;

  template <class TagType>
  inline static std::enable_if_t<std::is_void<TagType>::value> execute_functor(
      const FunctorType &functor, const Policy &policy, const int league_rank,
      char *local_buffer, const std::size_t local_buffer_size) {
    functor(Member(policy, 0, league_rank, local_buffer, local_buffer_size));
  }

  template <class TagType>
  inline static std::enable_if_t<!std::is_void<TagType>::value> execute_functor(
      const FunctorType &functor, const Policy &policy, const int league_rank,
      char *local_buffer, const std::size_t local_buffer_size) {
    const TagType t{};
    functor(t, Member(policy, 0, league_rank, local_buffer, local_buffer_size));
  }

  template <class TagType>
  inline static std::enable_if_t<std::is_void<TagType>::value>
  execute_functor_range(const FunctorType &functor, const Policy &policy,
                        const int league_rank_begin, const int league_rank_end,
                        char *local_buffer,
                        const std::size_t local_buffer_size) {
    for (int league_rank = league_rank_begin; league_rank < league_rank_end;
         ++league_rank) {
      functor(Member(policy, 0, league_rank, local_buffer, local_buffer_size));
    }
  }

  template <class TagType>
  inline static std::enable_if_t<!std::is_void<TagType>::value>
  execute_functor_range(const FunctorType &functor, const Policy &policy,
                        const int league_rank_begin, const int league_rank_end,
                        char *local_buffer,
                        const std::size_t local_buffer_size) {
    const TagType t{};
    for (int league_rank = league_rank_begin; league_rank < league_rank_end;
         ++league_rank) {
      functor(t,
              Member(policy, 0, league_rank, local_buffer, local_buffer_size));
    }
  }

 public:
  void execute() const { dispatch_execute_task(this, m_policy.space()); }

  inline void execute_task() const {
    // See [note 1] for an explanation.
    Kokkos::Experimental::HPX::reset_on_exit_parallel reset_on_exit(
        m_policy.space());

    const int num_worker_threads = Kokkos::Experimental::HPX::concurrency();

    thread_buffer &buffer = m_policy.space().impl_get_buffer();
    buffer.resize(num_worker_threads, m_shared);

    auto exec = Kokkos::Experimental::HPX::impl_get_executor();

    using hpx::execution::par;
    using hpx::execution::static_chunk_size;

#if KOKKOS_HPX_IMPLEMENTATION == 0
    using hpx::for_loop;

    for_loop(
        par.on(exec).with(static_chunk_size(m_policy.chunk_size())), 0,
        m_policy.league_size(), [this, &buffer](const int league_rank) {
          execute_functor<WorkTag>(
              m_functor, m_policy, league_rank,
              buffer.get(Kokkos::Experimental::HPX::impl_hardware_thread_id()),
              m_shared);
        });

#elif KOKKOS_HPX_IMPLEMENTATION == 1
    using hpx::for_loop_strided;

    for_loop_strided(
        par.on(exec), 0, m_policy.league_size(), m_policy.chunk_size(),
        [this, &buffer](const int league_rank_begin) {
          const int league_rank_end =
              (std::min)(league_rank_begin + m_policy.chunk_size(),
                         m_policy.league_size());
          execute_functor_range<WorkTag>(
              m_functor, m_policy, league_rank_begin, league_rank_end,
              buffer.get(Kokkos::Experimental::HPX::impl_hardware_thread_id()),
              m_shared);
        });
#endif
  }

  ParallelFor(const FunctorType &arg_functor, const Policy &arg_policy)
      : m_functor(arg_functor),
        m_policy(arg_policy),
        m_league(arg_policy.league_size()),
        m_shared(arg_policy.scratch_size(0) + arg_policy.scratch_size(1) +
                 FunctorTeamShmemSize<FunctorType>::value(
                     arg_functor, arg_policy.team_size())) {}
};

template <class FunctorType, class ReducerType, class... Properties>
class ParallelReduce<FunctorType, Kokkos::TeamPolicy<Properties...>,
                     ReducerType, Kokkos::Experimental::HPX> {
 private:
  using Policy  = TeamPolicyInternal<Kokkos::Experimental::HPX, Properties...>;
  using Member  = typename Policy::member_type;
  using WorkTag = typename Policy::work_tag;
  using ReducerConditional =
      Kokkos::Impl::if_c<std::is_same<InvalidType, ReducerType>::value,
                         FunctorType, ReducerType>;
  using ReducerTypeFwd = typename ReducerConditional::type;
  using Analysis =
      FunctorAnalysis<FunctorPatternInterface::REDUCE, Policy, ReducerTypeFwd>;
  using pointer_type   = typename Analysis::pointer_type;
  using reference_type = typename Analysis::reference_type;
  using value_type     = typename Analysis::value_type;

  const FunctorType m_functor;
  const int m_league;
  const Policy m_policy;
  const ReducerType m_reducer;
  pointer_type m_result_ptr;
  const std::size_t m_shared;

  bool m_force_synchronous;

  template <class TagType>
  inline static std::enable_if_t<std::is_void<TagType>::value> execute_functor(
      const FunctorType &functor, const Policy &policy, const int league_rank,
      char *local_buffer, const std::size_t local_buffer_size,
      reference_type update) {
    functor(Member(policy, 0, league_rank, local_buffer, local_buffer_size),
            update);
  }

  template <class TagType>
  inline static std::enable_if_t<!std::is_void<TagType>::value> execute_functor(
      const FunctorType &functor, const Policy &policy, const int league_rank,
      char *local_buffer, const std::size_t local_buffer_size,
      reference_type update) {
    const TagType t{};
    functor(t, Member(policy, 0, league_rank, local_buffer, local_buffer_size),
            update);
  }

  template <class TagType>
  inline static std::enable_if_t<std::is_void<TagType>::value>
  execute_functor_range(const FunctorType &functor, const Policy &policy,
                        const int league_rank_begin, const int league_rank_end,
                        char *local_buffer, const std::size_t local_buffer_size,
                        reference_type update) {
    for (int league_rank = league_rank_begin; league_rank < league_rank_end;
         ++league_rank) {
      functor(Member(policy, 0, league_rank, local_buffer, local_buffer_size),
              update);
    }
  }

  template <class TagType>
  inline static std::enable_if_t<!std::is_void<TagType>::value>
  execute_functor_range(const FunctorType &functor, const Policy &policy,
                        const int league_rank_begin, const int league_rank_end,
                        char *local_buffer, const std::size_t local_buffer_size,
                        reference_type update) {
    const TagType t{};
    for (int league_rank = league_rank_begin; league_rank < league_rank_end;
         ++league_rank) {
      functor(t,
              Member(policy, 0, league_rank, local_buffer, local_buffer_size),
              update);
    }
  }

 public:
  void execute() const {
    if (m_policy.league_size() * m_policy.team_size() == 0) {
      if (m_result_ptr) {
        typename Analysis::Reducer final_reducer(
            &ReducerConditional::select(m_functor, m_reducer));
        final_reducer.init(m_result_ptr);
        final_reducer.final(m_result_ptr);
      }
      return;
    }
    dispatch_execute_task(this, m_policy.space());
  }

  inline void execute_task() const {
    // See [note 1] for an explanation.
    Kokkos::Experimental::HPX::reset_on_exit_parallel reset_on_exit(
        m_policy.space());

    const int num_worker_threads = Kokkos::Experimental::HPX::concurrency();
    const std::size_t value_size =
        Analysis::value_size(ReducerConditional::select(m_functor, m_reducer));

    thread_buffer &buffer = m_policy.space().impl_get_buffer();
    buffer.resize(num_worker_threads, value_size + m_shared);

    auto exec = Kokkos::Experimental::HPX::impl_get_executor();

    using hpx::for_loop;
    using hpx::execution::par;
    using hpx::execution::static_chunk_size;

    typename Analysis::Reducer final_reducer(
        &ReducerConditional::select(m_functor, m_reducer));

#if KOKKOS_HPX_IMPLEMENTATION == 0

    for_loop(
        par.on(exec).with(static_chunk_size(1)), 0, num_worker_threads,
        [&buffer, final_reducer](const std::size_t t) {
          final_reducer.init(reinterpret_cast<pointer_type>(buffer.get(t)));
        });

    for_loop(par.on(exec).with(static_chunk_size(m_policy.chunk_size())), 0,
             m_policy.league_size(),
             [this, &buffer, value_size](const int league_rank) {
               std::size_t t =
                   Kokkos::Experimental::HPX::impl_hardware_thread_id();
               reference_type update = Analysis::Reducer::reference(
                   reinterpret_cast<pointer_type>(buffer.get(t)));

               execute_functor<WorkTag>(m_functor, m_policy, league_rank,
                                        buffer.get(t) + value_size, m_shared,
                                        update);
             });

#elif KOKKOS_HPX_IMPLEMENTATION == 1
    using hpx::for_loop_strided;

    for_loop(
        par.on(exec).with(static_chunk_size(1)), 0, num_worker_threads,
        [&buffer, final_reducer](std::size_t const t) {
          final_reducer.init(reinterpret_cast<pointer_type>(buffer.get(t)));
        });

    for_loop_strided(
        par.on(exec), 0, m_policy.league_size(), m_policy.chunk_size(),
        [this, &buffer, value_size](int const league_rank_begin) {
          std::size_t t = Kokkos::Experimental::HPX::impl_hardware_thread_id();
          reference_type update = Analysis::Reducer::reference(
              reinterpret_cast<pointer_type>(buffer.get(t)));
          const int league_rank_end =
              (std::min)(league_rank_begin + m_policy.chunk_size(),
                         m_policy.league_size());
          execute_functor_range<WorkTag>(
              m_functor, m_policy, league_rank_begin, league_rank_end,
              buffer.get(t) + value_size, m_shared, update);
        });
#endif

    const pointer_type ptr = reinterpret_cast<pointer_type>(buffer.get(0));
    for (int t = 1; t < num_worker_threads; ++t) {
      final_reducer.join(ptr, reinterpret_cast<pointer_type>(buffer.get(t)));
    }

    final_reducer.final(ptr);

    if (m_result_ptr) {
      const int n = Analysis::value_count(
          ReducerConditional::select(m_functor, m_reducer));

      for (int j = 0; j < n; ++j) {
        m_result_ptr[j] = ptr[j];
      }
    }
  }

  template <class ViewType>
  ParallelReduce(const FunctorType &arg_functor, const Policy &arg_policy,
                 const ViewType &arg_result,
                 std::enable_if_t<Kokkos::is_view<ViewType>::value &&
                                      !Kokkos::is_reducer<ReducerType>::value,
                                  void *> = nullptr)
      : m_functor(arg_functor),
        m_league(arg_policy.league_size()),
        m_policy(arg_policy),
        m_reducer(InvalidType()),
        m_result_ptr(arg_result.data()),
        m_shared(arg_policy.scratch_size(0) + arg_policy.scratch_size(1) +
                 FunctorTeamShmemSize<FunctorType>::value(
                     m_functor, arg_policy.team_size())),
        m_force_synchronous(!arg_result.impl_track().has_record()) {}

  inline ParallelReduce(const FunctorType &arg_functor, Policy arg_policy,
                        const ReducerType &reducer)
      : m_functor(arg_functor),
        m_league(arg_policy.league_size()),
        m_policy(arg_policy),
        m_reducer(reducer),
        m_result_ptr(reducer.view().data()),
        m_shared(arg_policy.scratch_size(0) + arg_policy.scratch_size(1) +
                 FunctorTeamShmemSize<FunctorType>::value(
                     arg_functor, arg_policy.team_size())),
        m_force_synchronous(!reducer.view().impl_track().has_record()) {}
};
}  // namespace Impl
}  // namespace Kokkos

namespace Kokkos {

template <typename iType>
KOKKOS_INLINE_FUNCTION
    Impl::TeamThreadRangeBoundariesStruct<iType, Impl::HPXTeamMember>
    TeamThreadRange(const Impl::HPXTeamMember &thread, const iType &count) {
  return Impl::TeamThreadRangeBoundariesStruct<iType, Impl::HPXTeamMember>(
      thread, count);
}

template <typename iType1, typename iType2>
KOKKOS_INLINE_FUNCTION Impl::TeamThreadRangeBoundariesStruct<
    std::common_type_t<iType1, iType2>, Impl::HPXTeamMember>
TeamThreadRange(const Impl::HPXTeamMember &thread, const iType1 &i_begin,
                const iType2 &i_end) {
  using iType = std::common_type_t<iType1, iType2>;
  return Impl::TeamThreadRangeBoundariesStruct<iType, Impl::HPXTeamMember>(
      thread, iType(i_begin), iType(i_end));
}

template <typename iType>
KOKKOS_INLINE_FUNCTION
    Impl::TeamThreadRangeBoundariesStruct<iType, Impl::HPXTeamMember>
    TeamVectorRange(const Impl::HPXTeamMember &thread, const iType &count) {
  return Impl::TeamThreadRangeBoundariesStruct<iType, Impl::HPXTeamMember>(
      thread, count);
}

template <typename iType1, typename iType2>
KOKKOS_INLINE_FUNCTION Impl::TeamThreadRangeBoundariesStruct<
    std::common_type_t<iType1, iType2>, Impl::HPXTeamMember>
TeamVectorRange(const Impl::HPXTeamMember &thread, const iType1 &i_begin,
                const iType2 &i_end) {
  using iType = std::common_type_t<iType1, iType2>;
  return Impl::TeamThreadRangeBoundariesStruct<iType, Impl::HPXTeamMember>(
      thread, iType(i_begin), iType(i_end));
}

template <typename iType>
KOKKOS_INLINE_FUNCTION
    Impl::ThreadVectorRangeBoundariesStruct<iType, Impl::HPXTeamMember>
    ThreadVectorRange(const Impl::HPXTeamMember &thread, const iType &count) {
  return Impl::ThreadVectorRangeBoundariesStruct<iType, Impl::HPXTeamMember>(
      thread, count);
}

template <typename iType1, typename iType2>
KOKKOS_INLINE_FUNCTION Impl::ThreadVectorRangeBoundariesStruct<
    std::common_type_t<iType1, iType2>, Impl::HPXTeamMember>
ThreadVectorRange(const Impl::HPXTeamMember &thread, const iType1 &i_begin,
                  const iType2 &i_end) {
  using iType = std::common_type_t<iType1, iType2>;
  return Impl::ThreadVectorRangeBoundariesStruct<iType, Impl::HPXTeamMember>(
      thread, iType(i_begin), iType(i_end));
}

KOKKOS_INLINE_FUNCTION
Impl::ThreadSingleStruct<Impl::HPXTeamMember> PerTeam(
    const Impl::HPXTeamMember &thread) {
  return Impl::ThreadSingleStruct<Impl::HPXTeamMember>(thread);
}

KOKKOS_INLINE_FUNCTION
Impl::VectorSingleStruct<Impl::HPXTeamMember> PerThread(
    const Impl::HPXTeamMember &thread) {
  return Impl::VectorSingleStruct<Impl::HPXTeamMember>(thread);
}

/** \brief  Inter-thread parallel_for. Executes lambda(iType i) for each
 * i=0..N-1.
 *
 * The range i=0..N-1 is mapped to all threads of the the calling thread team.
 */
template <typename iType, class Lambda>
KOKKOS_INLINE_FUNCTION void parallel_for(
    const Impl::TeamThreadRangeBoundariesStruct<iType, Impl::HPXTeamMember>
        &loop_boundaries,
    const Lambda &lambda) {
  for (iType i = loop_boundaries.start; i < loop_boundaries.end;
       i += loop_boundaries.increment)
    lambda(i);
}

/** \brief  Inter-thread vector parallel_reduce. Executes lambda(iType i,
 * ValueType & val) for each i=0..N-1.
 *
 * The range i=0..N-1 is mapped to all threads of the the calling thread team
 * and a summation of val is performed and put into result.
 */
template <typename iType, class Lambda, typename ValueType>
KOKKOS_INLINE_FUNCTION void parallel_reduce(
    const Impl::TeamThreadRangeBoundariesStruct<iType, Impl::HPXTeamMember>
        &loop_boundaries,
    const Lambda &lambda, ValueType &result) {
  result = ValueType();
  for (iType i = loop_boundaries.start; i < loop_boundaries.end;
       i += loop_boundaries.increment) {
    lambda(i, result);
  }
}

/** \brief  Intra-thread vector parallel_for. Executes lambda(iType i) for each
 * i=0..N-1.
 *
 * The range i=0..N-1 is mapped to all vector lanes of the the calling thread.
 */
template <typename iType, class Lambda>
KOKKOS_INLINE_FUNCTION void parallel_for(
    const Impl::ThreadVectorRangeBoundariesStruct<iType, Impl::HPXTeamMember>
        &loop_boundaries,
    const Lambda &lambda) {
#ifdef KOKKOS_ENABLE_PRAGMA_IVDEP
#pragma ivdep
#endif
  for (iType i = loop_boundaries.start; i < loop_boundaries.end;
       i += loop_boundaries.increment) {
    lambda(i);
  }
}

/** \brief  Intra-thread vector parallel_reduce. Executes lambda(iType i,
 * ValueType & val) for each i=0..N-1.
 *
 * The range i=0..N-1 is mapped to all vector lanes of the the calling thread
 * and a summation of val is performed and put into result.
 */
template <typename iType, class Lambda, typename ValueType>
KOKKOS_INLINE_FUNCTION void parallel_reduce(
    const Impl::ThreadVectorRangeBoundariesStruct<iType, Impl::HPXTeamMember>
        &loop_boundaries,
    const Lambda &lambda, ValueType &result) {
  result = ValueType();
#ifdef KOKKOS_ENABLE_PRAGMA_IVDEP
#pragma ivdep
#endif
  for (iType i = loop_boundaries.start; i < loop_boundaries.end;
       i += loop_boundaries.increment) {
    lambda(i, result);
  }
}

template <typename iType, class Lambda, typename ReducerType>
KOKKOS_INLINE_FUNCTION void parallel_reduce(
    const Impl::TeamThreadRangeBoundariesStruct<iType, Impl::HPXTeamMember>
        &loop_boundaries,
    const Lambda &lambda, const ReducerType &reducer) {
  reducer.init(reducer.reference());
  for (iType i = loop_boundaries.start; i < loop_boundaries.end;
       i += loop_boundaries.increment) {
    lambda(i, reducer.reference());
  }
}

template <typename iType, class Lambda, typename ReducerType>
KOKKOS_INLINE_FUNCTION void parallel_reduce(
    const Impl::ThreadVectorRangeBoundariesStruct<iType, Impl::HPXTeamMember>
        &loop_boundaries,
    const Lambda &lambda, const ReducerType &reducer) {
  reducer.init(reducer.reference());
#ifdef KOKKOS_ENABLE_PRAGMA_IVDEP
#pragma ivdep
#endif
  for (iType i = loop_boundaries.start; i < loop_boundaries.end;
       i += loop_boundaries.increment) {
    lambda(i, reducer.reference());
  }
}

template <typename iType, class FunctorType>
KOKKOS_INLINE_FUNCTION void parallel_scan(
    Impl::TeamThreadRangeBoundariesStruct<iType, Impl::HPXTeamMember> const
        &loop_boundaries,
    const FunctorType &lambda) {
  using value_type = typename Kokkos::Impl::FunctorAnalysis<
      Kokkos::Impl::FunctorPatternInterface::SCAN, void,
      FunctorType>::value_type;

  value_type scan_val = value_type();

  // Intra-member scan
  for (iType i = loop_boundaries.start; i < loop_boundaries.end;
       i += loop_boundaries.increment) {
    lambda(i, scan_val, false);
  }

  // 'scan_val' output is the exclusive prefix sum
  scan_val = loop_boundaries.thread.team_scan(scan_val);

  for (iType i = loop_boundaries.start; i < loop_boundaries.end;
       i += loop_boundaries.increment) {
    lambda(i, scan_val, true);
  }
}

/** \brief  Intra-thread vector parallel exclusive prefix sum. Executes
 * lambda(iType i, ValueType & val, bool final) for each i=0..N-1.
 *
 * The range i=0..N-1 is mapped to all vector lanes in the thread and a scan
 * operation is performed. Depending on the target execution space the operator
 * might be called twice: once with final=false and once with final=true. When
 * final==true val contains the prefix sum value. The contribution of this "i"
 * needs to be added to val no matter whether final==true or not. In a serial
 * execution (i.e. team_size==1) the operator is only called once with
 * final==true. Scan_val will be set to the final sum value over all vector
 */
template <typename iType, class FunctorType>
KOKKOS_INLINE_FUNCTION void parallel_scan(
    const Impl::ThreadVectorRangeBoundariesStruct<iType, Impl::HPXTeamMember>
        &loop_boundaries,
    const FunctorType &lambda) {
  using value_type =
      typename Impl::FunctorAnalysis<Impl::FunctorPatternInterface::SCAN,
                                     TeamPolicy<Experimental::HPX>,
                                     FunctorType>::value_type;

  value_type scan_val = value_type();

#ifdef KOKKOS_ENABLE_PRAGMA_IVDEP
#pragma ivdep
#endif
  for (iType i = loop_boundaries.start; i < loop_boundaries.end;
       i += loop_boundaries.increment) {
    lambda(i, scan_val, true);
  }
}

/** \brief  Intra-thread vector parallel scan with reducer
 *
 */
template <typename iType, class FunctorType, typename ReducerType>
KOKKOS_INLINE_FUNCTION std::enable_if_t<Kokkos::is_reducer<ReducerType>::value>
parallel_scan(
    const Impl::ThreadVectorRangeBoundariesStruct<iType, Impl::HPXTeamMember>
        &loop_boundaries,
    const FunctorType &lambda, const ReducerType &reducer) {
  typename ReducerType::value_type scan_val;
  reducer.init(scan_val);

#ifdef KOKKOS_ENABLE_PRAGMA_IVDEP
#pragma ivdep
#endif
  for (iType i = loop_boundaries.start; i < loop_boundaries.end;
       i += loop_boundaries.increment) {
    lambda(i, scan_val, true);
  }
}

template <class FunctorType>
KOKKOS_INLINE_FUNCTION void single(
    const Impl::VectorSingleStruct<Impl::HPXTeamMember> &,
    const FunctorType &lambda) {
  lambda();
}

template <class FunctorType>
KOKKOS_INLINE_FUNCTION void single(
    const Impl::ThreadSingleStruct<Impl::HPXTeamMember> &,
    const FunctorType &lambda) {
  lambda();
}

template <class FunctorType, class ValueType>
KOKKOS_INLINE_FUNCTION void single(
    const Impl::VectorSingleStruct<Impl::HPXTeamMember> &,
    const FunctorType &lambda, ValueType &val) {
  lambda(val);
}

template <class FunctorType, class ValueType>
KOKKOS_INLINE_FUNCTION void single(
    const Impl::ThreadSingleStruct<Impl::HPXTeamMember> &,
    const FunctorType &lambda, ValueType &val) {
  lambda(val);
}

}  // namespace Kokkos

#include <HPX/Kokkos_HPX_Task.hpp>

#endif /* #if defined( KOKKOS_ENABLE_HPX ) */
#endif /* #ifndef KOKKOS_HPX_HPP */

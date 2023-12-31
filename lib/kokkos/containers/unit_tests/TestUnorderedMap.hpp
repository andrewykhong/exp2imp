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

#ifndef KOKKOS_TEST_UNORDERED_MAP_HPP
#define KOKKOS_TEST_UNORDERED_MAP_HPP

#include <gtest/gtest.h>
#include <iostream>
#include <Kokkos_UnorderedMap.hpp>

namespace Test {

namespace Impl {

template <typename MapType, bool Near = false>
struct TestInsert {
  using map_type        = MapType;
  using execution_space = typename map_type::execution_space;
  using value_type      = uint32_t;

  map_type map;
  uint32_t inserts;
  uint32_t collisions;

  TestInsert(map_type arg_map, uint32_t arg_inserts, uint32_t arg_collisions)
      : map(arg_map), inserts(arg_inserts), collisions(arg_collisions) {}

  void testit(bool rehash_on_fail = true) {
    execution_space().fence();

    uint32_t failed_count = 0;
    do {
      failed_count = 0;
      Kokkos::parallel_reduce(inserts, *this, failed_count);

      if (rehash_on_fail && failed_count > 0u) {
        const uint32_t new_capacity = map.capacity() +
                                      ((map.capacity() * 3ull) / 20u) +
                                      failed_count / collisions;
        map.rehash(new_capacity);
      }
    } while (rehash_on_fail && failed_count > 0u);

    execution_space().fence();
  }

  KOKKOS_INLINE_FUNCTION
  void init(value_type &failed_count) const { failed_count = 0; }

  KOKKOS_INLINE_FUNCTION
  void join(value_type &failed_count, const value_type &count) const {
    failed_count += count;
  }

  KOKKOS_INLINE_FUNCTION
  void operator()(uint32_t i, value_type &failed_count) const {
    const uint32_t key = Near ? i / collisions : i % (inserts / collisions);
    if (map.insert(key, i).failed()) ++failed_count;
  }
};

template <typename MapType, bool Near>
struct TestErase {
  using self_type = TestErase<MapType, Near>;

  using map_type        = MapType;
  using execution_space = typename MapType::execution_space;

  map_type m_map;
  uint32_t m_num_erase;
  uint32_t m_num_duplicates;

  TestErase(map_type map, uint32_t num_erases, uint32_t num_duplicates)
      : m_map(map), m_num_erase(num_erases), m_num_duplicates(num_duplicates) {}

  void testit() {
    execution_space().fence();
    Kokkos::parallel_for(m_num_erase, *this);
    execution_space().fence();
  }

  KOKKOS_INLINE_FUNCTION
  void operator()(typename execution_space::size_type i) const {
    if (Near) {
      m_map.erase(i / m_num_duplicates);
    } else {
      m_map.erase(i % (m_num_erase / m_num_duplicates));
    }
  }
};

template <typename MapType>
struct TestFind {
  using map_type        = MapType;
  using execution_space = typename MapType::execution_space::execution_space;
  using value_type      = uint32_t;

  map_type m_map;
  uint32_t m_num_insert;
  uint32_t m_num_duplicates;
  uint32_t m_max_key;

  TestFind(map_type map, uint32_t num_inserts, uint32_t num_duplicates)
      : m_map(map),
        m_num_insert(num_inserts),
        m_num_duplicates(num_duplicates),
        m_max_key(((num_inserts + num_duplicates) - 1) / num_duplicates) {}

  void testit(value_type &errors) {
    execution_space().fence();
    Kokkos::parallel_reduce(m_map.capacity(), *this, errors);
    execution_space().fence();
  }

  KOKKOS_INLINE_FUNCTION
  static void init(value_type &dst) { dst = 0; }

  KOKKOS_INLINE_FUNCTION
  static void join(value_type &dst, const value_type &src) { dst += src; }

  KOKKOS_INLINE_FUNCTION
  void operator()(typename execution_space::size_type i,
                  value_type &errors) const {
    const bool expect_to_find_i =
        (i < typename execution_space::size_type(m_max_key));

    const bool exists = m_map.exists(i);

    if (expect_to_find_i && !exists) ++errors;
    if (!expect_to_find_i && exists) ++errors;
  }
};

}  // namespace Impl

// MSVC reports a syntax error for this test.
// WORKAROUND MSVC
#ifndef _WIN32
template <typename Device>
void test_insert(uint32_t num_nodes, uint32_t num_inserts,
                 uint32_t num_duplicates, bool near) {
  using map_type = Kokkos::UnorderedMap<uint32_t, uint32_t, Device>;
  using const_map_type =
      Kokkos::UnorderedMap<const uint32_t, const uint32_t, Device>;

  const uint32_t expected_inserts =
      (num_inserts + num_duplicates - 1u) / num_duplicates;

  map_type map;
  map.rehash(num_nodes, false);

  if (near) {
    Impl::TestInsert<map_type, true> test_insert(map, num_inserts,
                                                 num_duplicates);
    test_insert.testit();
  } else {
    Impl::TestInsert<map_type, false> test_insert(map, num_inserts,
                                                  num_duplicates);
    test_insert.testit();
  }

  const bool print_list = false;
  if (print_list) {
    Kokkos::Impl::UnorderedMapPrint<map_type> f(map);
    f.apply();
  }

  const uint32_t map_size = map.size();

  ASSERT_FALSE(map.failed_insert());
  {
    EXPECT_EQ(expected_inserts, map_size);

    {
      uint32_t find_errors = 0;
      Impl::TestFind<const_map_type> test_find(map, num_inserts,
                                               num_duplicates);
      test_find.testit(find_errors);
      EXPECT_EQ(0u, find_errors);
    }

    map.begin_erase();
    Impl::TestErase<map_type, false> test_erase(map, num_inserts,
                                                num_duplicates);
    test_erase.testit();
    map.end_erase();
    EXPECT_EQ(0u, map.size());
  }
}
#endif

template <typename Device>
void test_failed_insert(uint32_t num_nodes) {
  using map_type = Kokkos::UnorderedMap<uint32_t, uint32_t, Device>;

  map_type map(num_nodes);
  Impl::TestInsert<map_type> test_insert(map, 2u * num_nodes, 1u);
  test_insert.testit(false /*don't rehash on fail*/);
  typename Device::execution_space().fence();

  EXPECT_TRUE(map.failed_insert());
}

template <typename Device>
void test_deep_copy(uint32_t num_nodes) {
  using map_type = Kokkos::UnorderedMap<uint32_t, uint32_t, Device>;
  using const_map_type =
      Kokkos::UnorderedMap<const uint32_t, const uint32_t, Device>;

  using host_map_type = typename map_type::HostMirror;

  map_type map;
  map.rehash(num_nodes, false);

  {
    Impl::TestInsert<map_type> test_insert(map, num_nodes, 1);
    test_insert.testit();
    ASSERT_EQ(map.size(), num_nodes);
    ASSERT_FALSE(map.failed_insert());
    {
      uint32_t find_errors = 0;
      Impl::TestFind<map_type> test_find(map, num_nodes, 1);
      test_find.testit(find_errors);
      EXPECT_EQ(find_errors, 0u);
    }
  }

  host_map_type hmap;
  Kokkos::deep_copy(hmap, map);

  ASSERT_EQ(map.size(), hmap.size());
  ASSERT_EQ(map.capacity(), hmap.capacity());
  {
    uint32_t find_errors = 0;
    Impl::TestFind<host_map_type> test_find(hmap, num_nodes, 1);
    test_find.testit(find_errors);
    EXPECT_EQ(find_errors, 0u);
  }

  map_type mmap;
  Kokkos::deep_copy(mmap, hmap);

  const_map_type cmap = mmap;

  EXPECT_EQ(cmap.size(), num_nodes);

  {
    uint32_t find_errors = 0;
    Impl::TestFind<const_map_type> test_find(cmap, num_nodes, 1);
    test_find.testit(find_errors);
    EXPECT_EQ(find_errors, 0u);
  }
}

#if !defined(_WIN32)
TEST(TEST_CATEGORY, UnorderedMap_insert) {
#if defined(KOKKOS_ENABLE_CUDA) && \
    defined(KOKKOS_COMPILER_NVHPC)  // FIXME_NVHPC
  if constexpr (std::is_same_v<TEST_EXECSPACE, Kokkos::Cuda>) {
    GTEST_SKIP() << "unit test is hanging from index 0";
  }
#endif
  for (int i = 0; i < 500; ++i) {
    test_insert<TEST_EXECSPACE>(100000, 90000, 100, true);
    test_insert<TEST_EXECSPACE>(100000, 90000, 100, false);
  }
}
#endif

TEST(TEST_CATEGORY, UnorderedMap_failed_insert) {
  for (int i = 0; i < 1000; ++i) test_failed_insert<TEST_EXECSPACE>(10000);
}

TEST(TEST_CATEGORY, UnorderedMap_deep_copy) {
#if defined(KOKKOS_ENABLE_CUDA) && \
    defined(KOKKOS_COMPILER_NVHPC)  // FIXME_NVHPC
  if constexpr (std::is_same_v<TEST_EXECSPACE, Kokkos::Cuda>) {
    GTEST_SKIP() << "unit test is hanging from index 0";
  }
#endif
  for (int i = 0; i < 2; ++i) test_deep_copy<TEST_EXECSPACE>(10000);
}

TEST(TEST_CATEGORY, UnorderedMap_valid_empty) {
  using Key   = int;
  using Value = int;
  using Map   = Kokkos::UnorderedMap<Key, Value, TEST_EXECSPACE>;

  Map m{};
  Map n{};
  n = Map{m.capacity()};
  n.rehash(m.capacity());
  Kokkos::deep_copy(n, m);
  ASSERT_TRUE(m.is_allocated());
  ASSERT_TRUE(n.is_allocated());
}

TEST(TEST_CATEGORY, UnorderedMap_clear_zero_size) {
  using Map =
      Kokkos::UnorderedMap<int, void, Kokkos::DefaultHostExecutionSpace>;

  Map m(11);
  ASSERT_EQ(0u, m.size());

  m.insert(2);
  m.insert(3);
  m.insert(5);
  m.insert(7);
  ASSERT_EQ(4u, m.size());
  m.rehash(0);
  ASSERT_EQ(128u, m.capacity());
  ASSERT_EQ(4u, m.size());

  m.clear();
  ASSERT_EQ(0u, m.size());
}

}  // namespace Test

#endif  // KOKKOS_TEST_UNORDERED_MAP_HPP

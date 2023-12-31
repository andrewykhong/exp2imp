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

#include <Kokkos_Core.hpp>
#include <gtest/gtest.h>
#include <PerfTest_Category.hpp>
#include <Kokkos_Random.hpp>

#ifdef KOKKOS_ENABLE_CXX11_DISPATCH_LAMBDA
namespace Test {
template <class Scalar>
void custom_reduction_test(int N, int R, int num_trials) {
  Kokkos::Random_XorShift64_Pool<> rand_pool(183291);
  Kokkos::View<Scalar*> a("A", N);
  Kokkos::fill_random(a, rand_pool, 1.0);

  Scalar max;

  int team_size = 32;
  if (team_size > Kokkos::DefaultExecutionSpace().concurrency())
    team_size = Kokkos::DefaultExecutionSpace().concurrency();
  // Warm up
  Kokkos::parallel_reduce(
      Kokkos::TeamPolicy<>(N / 1024, team_size),
      KOKKOS_LAMBDA(const Kokkos::TeamPolicy<>::member_type& team,
                    Scalar& lmax) {
        Scalar team_max = Scalar(0);
        for (int rr = 0; rr < R; rr++) {
          int i = team.league_rank();
          Kokkos::parallel_reduce(
              Kokkos::TeamThreadRange(team, 32),
              [&](const int& j, Scalar& thread_max) {
                Scalar t_max = Scalar(0);
                Kokkos::parallel_reduce(
                    Kokkos::ThreadVectorRange(team, 32),
                    [&](const int& k, Scalar& max_) {
                      const Scalar val = a((i * 32 + j) * 32 + k);
                      if (val > max_) max_ = val;
                      if ((k == 11) && (j == 17) && (i == 2)) max_ = 11.5;
                    },
                    Kokkos::Max<Scalar>(t_max));
                if (t_max > thread_max) thread_max = t_max;
              },
              Kokkos::Max<Scalar>(team_max));
        }
        if (team_max > lmax) lmax = team_max;
      },
      Kokkos::Max<Scalar>(max));

  // Timing
  Kokkos::Timer timer;
  for (int r = 0; r < num_trials; r++) {
    Kokkos::parallel_reduce(
        Kokkos::TeamPolicy<>(N / 1024, team_size),
        KOKKOS_LAMBDA(const Kokkos::TeamPolicy<>::member_type& team,
                      Scalar& lmax) {
          Scalar team_max = Scalar(0);
          for (int rr = 0; rr < R; rr++) {
            int i = team.league_rank();
            Kokkos::parallel_reduce(
                Kokkos::TeamThreadRange(team, 32),
                [&](const int& j, Scalar& thread_max) {
                  Scalar t_max = Scalar(0);
                  Kokkos::parallel_reduce(
                      Kokkos::ThreadVectorRange(team, 32),
                      [&](const int& k, Scalar& max_) {
                        const Scalar val = a((i * 32 + j) * 32 + k);
                        if (val > max_) max_ = val;
                        if ((k == 11) && (j == 17) && (i == 2)) max_ = 11.5;
                      },
                      Kokkos::Max<Scalar>(t_max));
                  if (t_max > thread_max) thread_max = t_max;
                },
                Kokkos::Max<Scalar>(team_max));
          }
          if (team_max > lmax) lmax = team_max;
        },
        Kokkos::Max<Scalar>(max));
  }
  double time = timer.seconds();
  printf("%e %e %e\n", time,
         1.0 * N * R * num_trials * sizeof(Scalar) / time / 1024 / 1024 / 1024,
         max);
}

TEST(default_exec, custom_reduction) {
  int N          = 100000;
  int R          = 1000;
  int num_trials = 1;

  if (command_line_num_args() > 1) N = std::stoi(command_line_arg(1));
  if (command_line_num_args() > 2) R = std::stoi(command_line_arg(2));
  if (command_line_num_args() > 3) num_trials = std::stoi(command_line_arg(3));
  custom_reduction_test<double>(N, R, num_trials);
}
}  // namespace Test
#endif

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

#include <gtest/gtest.h>
#include <cstdlib>

#include <Kokkos_Core.hpp>

namespace Test {
int command_line_num_args(int n = 0) {
  static int n_args = 0;
  if (n > 0) n_args = n;
  return n_args;
}

const char* command_line_arg(int k, char** input_args = nullptr) {
  static char** args;
  if (input_args != nullptr) args = input_args;
  if (command_line_num_args() > k)
    return args[k];
  else
    return nullptr;
}

}  // namespace Test

int main(int argc, char* argv[]) {
  ::testing::InitGoogleTest(&argc, argv);
  Kokkos::initialize(argc, argv);

  (void)Test::command_line_num_args(argc);
  (void)Test::command_line_arg(0, argv);

  int result = RUN_ALL_TESTS();

  Kokkos::finalize();
  return result;
}

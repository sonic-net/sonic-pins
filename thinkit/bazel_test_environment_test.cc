// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#include "thinkit/bazel_test_environment.h"

#include <cstdlib>
#include <memory>
#include <string>
#include <vector>

// Switching benchmark dependency to third_party seems to not output any
// benchmarking information when run.
#include "absl/memory/memory.h"
#include "absl/strings/string_view.h"
#include "benchmark/benchmark.h"
#include "gmock/gmock.h"
#include "google/protobuf/wrappers.pb.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "thinkit/test_environment.h"

namespace thinkit {
namespace {

using ::gutil::IsOk;
using ::testing::UnorderedElementsAre;

// -- Tests --------------------------------------------------------------------

constexpr absl::string_view kTestArtifact = "my_test_artifact.txt";

TEST(BazelTestEnvironmentTest, StoreTestArtifact) {
  std::unique_ptr<TestEnvironment> environment =
      absl::make_unique<BazelTestEnvironment>(/*mask_known_failures=*/true);
  EXPECT_OK(environment->StoreTestArtifact(kTestArtifact, "Hello, World!\n"));
  EXPECT_OK(environment->StoreTestArtifact(kTestArtifact, "Hello, Test!\n"));
}

TEST(BazelTestEnvironmentTest, AppendToTestArtifact) {
  std::unique_ptr<TestEnvironment> environment =
      absl::make_unique<BazelTestEnvironment>(/*mask_known_failures=*/true);
  EXPECT_OK(
      environment->AppendToTestArtifact(kTestArtifact, "Hello, World!\n"));
  EXPECT_OK(environment->AppendToTestArtifact(kTestArtifact, "Hello, Test!\n"));
}

// Sanity check to rule out crashes and error statuses with mixed appends and
// stores.
TEST(BazelTestEnvironmentTest, AppendStoreAppendTestArtifact) {
  std::unique_ptr<TestEnvironment> environment =
      absl::make_unique<BazelTestEnvironment>(/*mask_known_failures=*/true);
  EXPECT_OK(
      environment->AppendToTestArtifact(kTestArtifact, "Hello, World!\n"));
  EXPECT_OK(environment->StoreTestArtifact(kTestArtifact, "Hello, Test!\n"));
  EXPECT_OK(environment->AppendToTestArtifact(kTestArtifact,
                                              "Hello again, World!\n"));
}

TEST(BazelTestEnvironmentTest,
     BazelTestEnvironmentStoreAndAppendTestArtifactWithProto) {
  // Explicitly uses the BazelTestEnvironment to ensure that we inherit
  // definitions from TestEnvironment appropriately.
  std::unique_ptr<BazelTestEnvironment> environment =
      absl::make_unique<BazelTestEnvironment>(/*mask_known_failures=*/true);
  auto foo_proto = gutil::ParseProtoOrDie<google::protobuf::Int32Value>(R"pb(
    value: 42)pb");
  EXPECT_OK(environment->StoreTestArtifact(kTestArtifact, foo_proto));
  EXPECT_OK(environment->AppendToTestArtifact(kTestArtifact, foo_proto));
}

// Test that SetTestCaseID correctly calls its input function.
TEST(BazelTestEnvironmentTest, SetTestCaseIdCallsMemberFunction) {
  std::vector<std::string> stored_test_case_ids;
  std::string test_id = "1";

  std::unique_ptr<TestEnvironment> environment =
      absl::make_unique<BazelTestEnvironment>(
          /*mask_known_failures=*/true,
          /*set_test_case_ids=*/[&](const std::vector<std::string>&
                                        test_case_ids) {
            stored_test_case_ids = test_case_ids;
          });

  environment->SetTestCaseID(test_id);
  EXPECT_THAT(stored_test_case_ids, UnorderedElementsAre(test_id));
}

// SetTestCaseID should not crash even if the environment is constructed without
// a function.
TEST(BazelTestEnvironmentTest, SetTestCaseIdWorksForUnaryConstructor) {
  std::unique_ptr<TestEnvironment> environment =
      absl::make_unique<BazelTestEnvironment>(/*mask_known_failures=*/true);
  environment->SetTestCaseID("1");
}

// -- Benchmarks ---------------------------------------------------------------
//
// Best run with 'blaze test --test_arg=--benchmark_filter=all <target>'.
//
// Ideally, we would like to use 'benchy' for benchmarking purposes, but,
// because we are benchmarking a testing environment, it relies on being set
// up as a test environment.
//
// For now, one can manually set the environment variable TEST_TMPDIR, then run
// it with benchy, but do not expect that to remain feasible since we may rely
// on additional parts of the test environment in the future.

// The state specifies the size of the written string in Bytes.
void RunBenchmark(benchmark::State& state, bool truncate) {
  const int size = state.range(0);
  const std::string filename = "benchmark_file";
  BazelTestEnvironment env(false);

  std::string str(size, 'a');
  if (truncate) {
    for (auto s : state) {
      ASSERT_THAT(env.StoreTestArtifact(filename, str), IsOk());
    }
  } else {
    for (auto s : state) {
      ASSERT_THAT(env.AppendToTestArtifact(filename, str), IsOk());
    }
  }
  // Outputs number of iterations (items) per second.
  state.SetItemsProcessed(static_cast<int64_t>(state.iterations()));
}

void BM_Bazel_AppendToTestArtifact(benchmark::State& state) {
  RunBenchmark(state, /*truncate=*/false);
}

BENCHMARK(BM_Bazel_AppendToTestArtifact)
    ->Args({/*write_size in bytes=*/1})
    ->Args({1024})
    ->Args({1024 * 1024});

void BM_Bazel_StoreTestArtifact(benchmark::State& state) {
  RunBenchmark(state, /*truncate=*/true);
}

BENCHMARK(BM_Bazel_StoreTestArtifact)
    ->Args({/*write_size in bytes=*/1})
    ->Args({1024})
    ->Args({1024 * 1024});

// Benchmarks how performance of Append changes based on the size of the file
// that is appended to. Ideally, performance should not change at all, but this
// problem came up in a previous issue (b/193839478).
void BenchmarkAppendTimeBasedOnStartingSize(benchmark::State& state,
                                            int start_size, int append_size) {
  const std::string filename = "benchmark_file";
  BazelTestEnvironment env(false);

  // We create a file of the given size to start, then benchmark the time that
  // appends take.
  ASSERT_THAT(env.StoreTestArtifact(filename, std::string(start_size, 'a')),
              IsOk());
  std::string str(append_size, 'a');
  for (auto s : state) {
    ASSERT_THAT(env.AppendToTestArtifact(filename, str), IsOk());
  }

  // Causes number of iterations (items) per second to be output.
  state.SetItemsProcessed(static_cast<int64_t>(state.iterations()));
}

void BM_Bazel_AppendTimeBasedOnStartingSize(benchmark::State& state) {
  BenchmarkAppendTimeBasedOnStartingSize(state, /*start_size=*/state.range(0),
                                         /*append_size=*/state.range(1));
}

BENCHMARK(BM_Bazel_AppendTimeBasedOnStartingSize)
    ->Args({
        /*start_size in bytes=*/1,
        /*write_size in bytes=*/1024,
    })
    ->Args({1024, 1024})
    ->Args({1024 * 1024, 1024})
    ->Args({1024 * 1024 * 1024, 1024});

}  // namespace
}  // namespace thinkit

/* Copyright 2024 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#include "gutil/gutil/test_artifact_writer.h"

#include <string>
#include <vector>

// Switching benchmark dependency to third_party seems to not output any
// benchmarking information when run.
#include "absl/strings/string_view.h"
#include "benchmark/benchmark.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/test_artifact_writer_test.pb.h"

namespace gutil {
namespace {

using ::gutil::IsOk;

// -- Tests --------------------------------------------------------------------

constexpr absl::string_view kTestArtifact = "my_test_artifact.txt";

ArtifactWriterTestMessage GetTestProto() {
  ArtifactWriterTestMessage proto;
  proto.set_int_field(42);
  proto.set_string_field("Test proto string");
  return proto;
}

TEST(BazelTestArtifactWriterTest, StoreTestArtifact) {
  BazelTestArtifactWriter artifact_writer;
  EXPECT_OK(
      artifact_writer.StoreTestArtifact(kTestArtifact, "Hello, World!\n"));
  EXPECT_OK(artifact_writer.StoreTestArtifact(kTestArtifact, GetTestProto()));
}

TEST(BazelTestArtifactWriterTest, AppendToTestArtifact) {
  BazelTestArtifactWriter artifact_writer;
  EXPECT_OK(
      artifact_writer.AppendToTestArtifact(kTestArtifact, "Hello, World!\n"));
  EXPECT_OK(
      artifact_writer.AppendToTestArtifact(kTestArtifact, GetTestProto()));
}

// Sanity check to rule out crashes and error statuses with mixed appends and
// stores.
TEST(BazelTestArtifactWriterTest, AppendStoreAppendTestArtifact) {
  BazelTestArtifactWriter artifact_writer;
  EXPECT_OK(
      artifact_writer.AppendToTestArtifact(kTestArtifact, "Hello, World!\n"));
  EXPECT_OK(artifact_writer.StoreTestArtifact(kTestArtifact, "Hello, Test!\n"));
  EXPECT_OK(artifact_writer.AppendToTestArtifact(kTestArtifact,
                                                 "Hello again, World!\n"));
  EXPECT_OK(artifact_writer.StoreTestArtifact(kTestArtifact, GetTestProto()));
  EXPECT_OK(
      artifact_writer.AppendToTestArtifact(kTestArtifact, GetTestProto()));
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
  BazelTestArtifactWriter artifact_writer;

  std::string str(size, 'a');
  if (truncate) {
    for (auto s : state) {
      ASSERT_THAT(artifact_writer.StoreTestArtifact(filename, str), IsOk());
    }
  } else {
    for (auto s : state) {
      ASSERT_THAT(artifact_writer.AppendToTestArtifact(filename, str), IsOk());
    }
  }
  // Outputs number of iterations (items) per second.
  state.SetItemsProcessed(static_cast<int64_t>(state.iterations()));
}

void BM_AppendToTestArtifact(benchmark::State& state) {
  RunBenchmark(state, /*truncate=*/false);
}

BENCHMARK(BM_AppendToTestArtifact)
    ->Args({/*write_size in bytes=*/1})
    ->Args({1024})
    ->Args({1024 * 1024});

void BM_StoreTestArtifact(benchmark::State& state) {
  RunBenchmark(state, /*truncate=*/true);
}

BENCHMARK(BM_StoreTestArtifact)
    ->Args({/*write_size in bytes=*/1})
    ->Args({1024})
    ->Args({1024 * 1024});

// Benchmarks how performance of Append changes based on the size of the file
// that is appended to. Ideally, performance should not change at all, but this
// problem came up in a previous issue (b/193839478).
void BenchmarkAppendTimeBasedOnStartingSize(benchmark::State& state,
                                            int start_size, int append_size) {
  const std::string filename = "benchmark_file";
  BazelTestArtifactWriter artifact_writer;

  // We create a file of the given size to start, then benchmark the time that
  // appends take.
  ASSERT_THAT(
      artifact_writer.StoreTestArtifact(filename, std::string(start_size, 'a')),
      IsOk());
  std::string str(append_size, 'a');
  for (auto s : state) {
    ASSERT_THAT(artifact_writer.AppendToTestArtifact(filename, str), IsOk());
  }

  // Causes number of iterations (items) per second to be output.
  state.SetItemsProcessed(static_cast<int64_t>(state.iterations()));
}

void BM_AppendTimeBasedOnStartingSize(benchmark::State& state) {
  BenchmarkAppendTimeBasedOnStartingSize(state, /*start_size=*/state.range(0),
                                         /*append_size=*/state.range(1));
}

BENCHMARK(BM_AppendTimeBasedOnStartingSize)
    ->Args({
        /*start_size in bytes=*/1,
        /*write_size in bytes=*/1024,
    })
    ->Args({1024, 1024})
    ->Args({1024 * 1024, 1024})
    ->Args({1024 * 1024 * 1024, 1024});

}  // namespace
}  // namespace gutil

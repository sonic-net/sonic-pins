#include "thinkit/bazel_test_environment.h"

#include <cstdlib>
#include <memory>
#include <string>

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
using ::testing::StrEq;

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
  std::string stored_test_case_id;
  std::string test_id = "1";

  std::unique_ptr<TestEnvironment> environment =
      absl::make_unique<BazelTestEnvironment>(
          /*mask_known_failures=*/true,
          /*set_test_case_id=*/[&](absl::string_view test_case_id) {
            stored_test_case_id = test_case_id;
          });

  environment->SetTestCaseID(test_id);
  EXPECT_THAT(test_id, StrEq(stored_test_case_id));
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
// Best run with 'blaze test --benchmarks=all'.
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
}  // namespace
}  // namespace thinkit

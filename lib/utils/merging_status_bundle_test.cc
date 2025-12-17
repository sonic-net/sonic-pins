#include "lib/utils/merging_status_bundle.h"

#include <vector>

#include "absl/status/status.h"
#include "absl/synchronization/mutex.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"

namespace pins_test {
namespace {

using ::gutil::StatusIs;
using ::testing::AllOf;
using ::testing::HasSubstr;
using ::testing::UnorderedElementsAre;

TEST(MergingStatusBundleTest, Empty) {
  MergingStatusBundle bundle;
  EXPECT_OK(bundle.Join());
}

TEST(MergingStatusBundleTest, AllOk) {
  MergingStatusBundle bundle;
  bundle.Add([] { return absl::OkStatus(); });
  bundle.Add([] { return absl::OkStatus(); });
  bundle.Add([] { return absl::OkStatus(); });
  EXPECT_OK(bundle.Join());
}

TEST(MergingStatusBundleTest, AllPerformWork) {
  absl::Mutex mutex;
  std::vector<int> values;
  values.reserve(3);

  MergingStatusBundle bundle;
  bundle.Add([&] {
    absl::MutexLock lock(&mutex);
    values.push_back(1);
    return absl::OkStatus();
  });
  bundle.Add([&] {
    absl::MutexLock lock(&mutex);
    values.push_back(2);
    return absl::OkStatus();
  });
  bundle.Add([&] {
    absl::MutexLock lock(&mutex);
    values.push_back(3);
    return absl::OkStatus();
  });
  EXPECT_OK(bundle.Join());
  EXPECT_THAT(values, UnorderedElementsAre(1, 2, 3));
}

TEST(MergingStatusBundleTest, OneError) {
  MergingStatusBundle bundle;
  bundle.Add([] { return absl::OkStatus(); });
  bundle.Add([] { return absl::UnavailableError(""); });
  bundle.Add([] { return absl::OkStatus(); });
  EXPECT_THAT(bundle.Join(), StatusIs(absl::StatusCode::kUnavailable,
                                      Not(HasSubstr("Multiple"))));
}

TEST(MergingStatusBundleTest, MultipleSameErrors) {
  MergingStatusBundle bundle;
  bundle.Add([] { return absl::OkStatus(); });
  bundle.Add([] { return absl::UnavailableError("fail1"); });
  bundle.Add([] { return absl::UnavailableError("fail2"); });
  EXPECT_THAT(bundle.Join(),
              StatusIs(absl::StatusCode::kUnavailable,
                       AllOf(HasSubstr("Multiple"), HasSubstr("fail1"),
                             HasSubstr("fail2"))));
}

TEST(MergingStatusBundleTest, MultipleDifferentErrors) {
  MergingStatusBundle bundle;
  bundle.Add([] { return absl::OkStatus(); });
  bundle.Add([] { return absl::UnavailableError("fail1"); });
  bundle.Add([] { return absl::NotFoundError("fail2"); });
  EXPECT_THAT(bundle.Join(),
              StatusIs(absl::StatusCode::kInternal,
                       AllOf(HasSubstr("Multiple"), HasSubstr("fail1"),
                             HasSubstr("fail2"))));
}

}  // namespace
}  // namespace pins_test


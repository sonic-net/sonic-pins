// Copyright 2022 Google LLC
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
#include "p4rt_app/utils/event_data_tracker.h"

#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace p4rt_app {
namespace {

TEST(EventDataTracker, ReadingDoesNotClearData) {
  EventDataTracker<int> data(/*default_value=*/0);

  data.Increment(1);
  data.Increment(2);
  data.Increment(10);

  EXPECT_EQ(data.ReadData(), 13);
  EXPECT_EQ(data.ReadData(), 13);
}

TEST(EventDataTracker, ReadAndResetClearsDataAndResetsToTheDefault) {
  EventDataTracker<int> data(/*default_value=*/100);

  data.Increment(1);
  data.Increment(2);
  data.Increment(10);

  EXPECT_EQ(data.ReadDataAndReset(), 113);
  EXPECT_EQ(data.ReadDataAndReset(), 100);
}

TEST(EventDataTracker, ReadingMinAndMaxValues) {
  EventDataTracker<absl::Duration> data(/*default_value=*/absl::ZeroDuration());

  data += absl::Minutes(1);
  EXPECT_EQ(data.ReadMinValue(), absl::Seconds(60));
  EXPECT_EQ(data.ReadMaxValue(), absl::Seconds(60));

  data += absl::Seconds(121);
  EXPECT_EQ(data.ReadMinValue(), absl::Seconds(60));
  EXPECT_EQ(data.ReadMaxValue(), absl::Seconds(121));

  data += absl::Seconds(55);
  EXPECT_EQ(data.ReadMinValue(), absl::Seconds(55));
  EXPECT_EQ(data.ReadMaxValue(), absl::Seconds(121));

  data += absl::Minutes(2);
  EXPECT_EQ(data.ReadMinValue(), absl::Seconds(55));
  EXPECT_EQ(data.ReadMaxValue(), absl::Seconds(121));

  data.ReadDataAndReset();
  EXPECT_FALSE(data.ReadMinValue().has_value());
  EXPECT_FALSE(data.ReadMaxValue().has_value());
}

TEST(EventDataTracker, MinAndMaxDoNotReturnDataWhenIncrementHasNotBeenCalled) {
  EventDataTracker<int> data(/*default_value=*/100);

  EXPECT_FALSE(data.ReadMinValue().has_value());
  EXPECT_FALSE(data.ReadMaxValue().has_value());
}

TEST(EventDataTracker, CanIncrementWithOverloadedOperator) {
  EventDataTracker<absl::Duration> data(/*default_value=*/absl::ZeroDuration());

  data.Increment(absl::Seconds(1));
  data += absl::Minutes(1);

  EXPECT_EQ(data.ReadData(), absl::Seconds(61));
}

}  // namespace
}  // namespace p4rt_app

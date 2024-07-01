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
#include "p4rt_app/utils/metric_recorder.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "p4rt_app/sonic/adapters/fake_table_adapter.h"

namespace p4rt_app {
namespace {

using ::testing::_;
using ::testing::Contains;
using ::testing::Pair;

bool WaitUntil(std::function<bool()> goal, absl::Duration timeout) {
  absl::Time deadline = absl::Now() + timeout;
  while (!goal()) {
    if (absl::Now() >= deadline) {
      return false;
    }
    absl::SleepFor(absl::Milliseconds(1));
  }
  return true;
}

bool CheckCount(const std::vector<swss::FieldValueTuple>& values,
                absl::string_view exp_count) {
  for (const auto& value : values) {
    if (value.first == "count" && value.second == exp_count) {
      return true;
    }
  }
  return false;
}

class MetricRecorderTest : public ::testing::Test {
 public:
  MetricRecorderTest()
      : authn_table_("StateDb:AUTHN_TABLE"),
        authz_table_("StateDb:AUTHZ_TABLE") {
    auto authn_table_adapter =
        std::make_unique<sonic::FakeTableAdapter>(&authn_table_, "AUTHN_TABLE");
    auto authz_table_adapter =
        std::make_unique<sonic::FakeTableAdapter>(&authz_table_, "AUTHZ_TABLE");
    authn_table_adapter_ = authn_table_adapter.get();
    authz_table_adapter_ = authz_table_adapter.get();
    metric_recorder_ = std::make_unique<MetricRecorder>(
        "p4rt", /*size=*/2, absl::ZeroDuration(),
        std::move(authn_table_adapter), std::move(authz_table_adapter));
  }

 protected:
  sonic::FakeSonicDbTable authn_table_;
  sonic::FakeSonicDbTable authz_table_;
  sonic::FakeTableAdapter* authn_table_adapter_;
  sonic::FakeTableAdapter* authz_table_adapter_;
  std::unique_ptr<MetricRecorder> metric_recorder_;
};

TEST_F(MetricRecorderTest, PermittedAuthnIsLoggedInDb) {
  metric_recorder_->RecordAuthnSuccess("user");

  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authn_table_adapter_->exists("p4rt|success|user");
      },
      absl::Milliseconds(500)));
  EXPECT_THAT(authn_table_adapter_->get("p4rt|success|user"),
              Contains(Pair("count", "1")));
  EXPECT_THAT(authn_table_adapter_->get("p4rt|success|user"),
              Contains(Pair("timestamp", _)));
}

TEST_F(MetricRecorderTest, DeniedAuthnIsLoggedInDb) {
  metric_recorder_->RecordAuthnFailure("reason");

  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authn_table_adapter_->exists("p4rt|failure|reason");
      },
      absl::Milliseconds(500)));
  EXPECT_THAT(authn_table_adapter_->get("p4rt|failure|reason"),
              Contains(Pair("count", "1")));
  EXPECT_THAT(authn_table_adapter_->get("p4rt|failure|reason"),
              Contains(Pair("timestamp", _)));
}

TEST_F(MetricRecorderTest, PermittedAuthzIsLoggedInDb) {
  metric_recorder_->RecordAuthz(/*permitted=*/true, "service", "rpc");

  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|permitted");
      },
      absl::Milliseconds(500)));
  EXPECT_THAT(authz_table_adapter_->get("service|rpc|permitted"),
              Contains(Pair("count", "1")));
  EXPECT_THAT(authz_table_adapter_->get("service|rpc|permitted"),
              Contains(Pair("timestamp", _)));
}

TEST_F(MetricRecorderTest, DeniedAuthzIsLoggedInDb) {
  metric_recorder_->RecordAuthz(/*permitted=*/false, "service", "rpc");

  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|denied");
      },
      absl::Milliseconds(500)));
  EXPECT_THAT(authz_table_adapter_->get("service|rpc|denied"),
              Contains(Pair("count", "1")));
  EXPECT_THAT(authz_table_adapter_->get("service|rpc|denied"),
              Contains(Pair("timestamp", _)));
}

TEST_F(MetricRecorderTest, PermittedAuthnCountIncrements) {
  metric_recorder_->RecordAuthnSuccess("user");
  metric_recorder_->RecordAuthnSuccess("user");

  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authn_table_adapter_->exists("p4rt|success|user") &&
               CheckCount(authn_table_adapter_->get("p4rt|success|user"), "2");
      },
      absl::Milliseconds(500)));
}

TEST_F(MetricRecorderTest, DeniedAuthnCountIncrements) {
  metric_recorder_->RecordAuthnFailure("reason");
  metric_recorder_->RecordAuthnFailure("reason");

  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authn_table_adapter_->exists("p4rt|failure|reason") &&
               CheckCount(authn_table_adapter_->get("p4rt|failure|reason"),
                          "2");
      },
      absl::Milliseconds(500)));
}

TEST_F(MetricRecorderTest, PermittedAuthzCountIncrements) {
  metric_recorder_->RecordAuthz(/*permitted=*/true, "service", "rpc");
  metric_recorder_->RecordAuthz(/*permitted=*/true, "service", "rpc");

  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|permitted") &&
               CheckCount(authz_table_adapter_->get("service|rpc|permitted"),
                          "2");
      },
      absl::Milliseconds(500)));
}

TEST_F(MetricRecorderTest, DeniedAuthzCountIncrements) {
  metric_recorder_->RecordAuthz(/*permitted=*/false, "service", "rpc");
  metric_recorder_->RecordAuthz(/*permitted=*/false, "service", "rpc");

  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|denied") &&
               CheckCount(authz_table_adapter_->get("service|rpc|denied"), "2");
      },
      absl::Milliseconds(500)));
}

TEST_F(MetricRecorderTest, PermittedAuthnLastTimestamp) {
  metric_recorder_->RecordAuthnSuccess("user");
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authn_table_adapter_->exists("p4rt|success|user");
      },
      absl::Milliseconds(500)));
  auto values = authn_table_adapter_->get("p4rt|success|user");
  EXPECT_THAT(values, Contains(Pair("timestamp", _)));
  std::string timestamp1;
  for (const auto& value : values) {
    if (value.first == "timestamp") {
      timestamp1 = value.second;
      break;
    }
  }

  metric_recorder_->RecordAuthnSuccess("user");
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authn_table_adapter_->exists("p4rt|success|user") &&
               CheckCount(authn_table_adapter_->get("p4rt|success|user"), "2");
      },
      absl::Milliseconds(500)));
  values = authn_table_adapter_->get("p4rt|success|user");
  EXPECT_THAT(values, Contains(Pair("timestamp", _)));
  std::string timestamp2;
  for (const auto& value : values) {
    if (value.first == "timestamp") {
      timestamp2 = value.second;
      break;
    }
  }

  EXPECT_NE(timestamp1, timestamp2);
}

TEST_F(MetricRecorderTest, DeniedAuthnLastTimestamp) {
  metric_recorder_->RecordAuthnFailure("reason");
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authn_table_adapter_->exists("p4rt|failure|reason");
      },
      absl::Milliseconds(500)));
  auto values = authn_table_adapter_->get("p4rt|failure|reason");
  EXPECT_THAT(values, Contains(Pair("timestamp", _)));
  std::string timestamp1;
  for (const auto& value : values) {
    if (value.first == "timestamp") {
      timestamp1 = value.second;
      break;
    }
  }

  metric_recorder_->RecordAuthnFailure("reason");
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authn_table_adapter_->exists("p4rt|failure|reason") &&
               CheckCount(authn_table_adapter_->get("p4rt|failure|reason"),
                          "2");
      },
      absl::Milliseconds(500)));
  values = authn_table_adapter_->get("p4rt|failure|reason");
  EXPECT_THAT(values, Contains(Pair("timestamp", _)));
  std::string timestamp2;
  for (const auto& value : values) {
    if (value.first == "timestamp") {
      timestamp2 = value.second;
      break;
    }
  }

  EXPECT_NE(timestamp1, timestamp2);
}

TEST_F(MetricRecorderTest, PermittedAuthzLastTimestamp) {
  metric_recorder_->RecordAuthz(/*permitted=*/true, "service", "rpc");
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|permitted");
      },
      absl::Milliseconds(500)));
  auto values = authz_table_adapter_->get("service|rpc|permitted");
  EXPECT_THAT(values, Contains(Pair("timestamp", _)));
  std::string timestamp1;
  for (const auto& value : values) {
    if (value.first == "timestamp") {
      timestamp1 = value.second;
      break;
    }
  }

  metric_recorder_->RecordAuthz(/*permitted=*/true, "service", "rpc");
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|permitted") &&
               CheckCount(authz_table_adapter_->get("service|rpc|permitted"),
                          "2");
      },
      absl::Milliseconds(500)));
  values = authz_table_adapter_->get("service|rpc|permitted");
  EXPECT_THAT(values, Contains(Pair("timestamp", _)));
  std::string timestamp2;
  for (const auto& value : values) {
    if (value.first == "timestamp") {
      timestamp2 = value.second;
      break;
    }
  }

  EXPECT_NE(timestamp1, timestamp2);
}

TEST_F(MetricRecorderTest, DeniedAuthzLastTimestamp) {
  metric_recorder_->RecordAuthz(/*permitted=*/false, "service", "rpc");
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|denied");
      },
      absl::Milliseconds(500)));
  auto values = authz_table_adapter_->get("service|rpc|denied");
  EXPECT_THAT(values, Contains(Pair("timestamp", _)));
  std::string timestamp1;
  for (const auto& value : values) {
    if (value.first == "timestamp") {
      timestamp1 = value.second;
      break;
    }
  }

  metric_recorder_->RecordAuthz(/*permitted=*/false, "service", "rpc");
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|denied") &&
               CheckCount(authz_table_adapter_->get("service|rpc|denied"), "2");
      },
      absl::Milliseconds(500)));
  values = authz_table_adapter_->get("service|rpc|denied");
  EXPECT_THAT(values, Contains(Pair("timestamp", _)));
  std::string timestamp2;
  for (const auto& value : values) {
    if (value.first == "timestamp") {
      timestamp2 = value.second;
      break;
    }
  }

  EXPECT_NE(timestamp1, timestamp2);
}

TEST_F(MetricRecorderTest, AuthnCacheOverflowTest) {
  metric_recorder_->RecordAuthnFailure("reason1");
  metric_recorder_->RecordAuthnSuccess("user1");
  // Overwrite authn failure reason1.
  metric_recorder_->RecordAuthnSuccess("user2");
  // Overwrite authn success user1.
  // Now authn failure reason1 has count 1 since it was overwritten before.
  metric_recorder_->RecordAuthnFailure("reason1");
  absl::SleepFor(absl::Milliseconds(500));

  ASSERT_TRUE(authn_table_adapter_->exists("p4rt|failure|reason1"));
  ASSERT_TRUE(authn_table_adapter_->exists("p4rt|success|user2"));
  EXPECT_THAT(authn_table_adapter_->get("p4rt|failure|reason1"),
              Contains(Pair("count", "1")));
  EXPECT_THAT(authn_table_adapter_->get("p4rt|failure|reason1"),
              Contains(Pair("timestamp", _)));
  EXPECT_THAT(authn_table_adapter_->get("p4rt|success|user2"),
              Contains(Pair("count", "1")));
  EXPECT_THAT(authn_table_adapter_->get("p4rt|success|user2"),
              Contains(Pair("timestamp", _)));
}

TEST_F(MetricRecorderTest, AuthzCacheOverflowTest) {
  metric_recorder_->RecordAuthz(/*permitted=*/true, "service1", "rpc1");
  metric_recorder_->RecordAuthz(/*permitted=*/true, "service1", "rpc2");
  // Overwrite service1 rpc1.
  metric_recorder_->RecordAuthz(/*permitted=*/false, "service2", "rpc1");
  // Overwrite service1 rpc2.
  // Now service1 rpc1 has count 1 since it was overwritten before.
  metric_recorder_->RecordAuthz(/*permitted=*/true, "service1", "rpc1");
  absl::SleepFor(absl::Milliseconds(500));

  ASSERT_TRUE(authz_table_adapter_->exists("service1|rpc1|permitted"));
  ASSERT_TRUE(authz_table_adapter_->exists("service2|rpc1|denied"));
  EXPECT_THAT(authz_table_adapter_->get("service1|rpc1|permitted"),
              Contains(Pair("count", "1")));
  EXPECT_THAT(authz_table_adapter_->get("service1|rpc1|permitted"),
              Contains(Pair("timestamp", _)));
  EXPECT_THAT(authz_table_adapter_->get("service2|rpc1|denied"),
              Contains(Pair("count", "1")));
  EXPECT_THAT(authz_table_adapter_->get("service2|rpc1|denied"),
              Contains(Pair("timestamp", _)));
}

}  // namespace
}  // namespace p4rt_app

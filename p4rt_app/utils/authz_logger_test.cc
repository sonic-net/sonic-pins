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
#include "p4rt_app/utils/authz_logger.h"

#include <functional>
#include <memory>
#include <string>

#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "p4rt_app/sonic/adapters/fake_table_adapter.h"

namespace p4rt_app {
namespace {

using ::testing::AllOf;
using ::testing::Contains;
using ::testing::Pair;

MATCHER_P(StrAsIntGe, x, "") { return std::stoll(arg) >= x; }

MATCHER_P(StrAsIntLe, x, "") { return std::stoll(arg) <= x; }

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

class AuthzLoggerTest : public ::testing::Test {
 public:
  AuthzLoggerTest()
      : authn_table_("StateDb:AUTHN_TABLE"),
        authz_table_("StateDb:AUTHZ_TABLE") {
    auto authn_table_adapter =
        std::make_unique<sonic::FakeTableAdapter>(&authn_table_, "AUTHN_TABLE");
    auto authz_table_adapter =
        std::make_unique<sonic::FakeTableAdapter>(&authz_table_, "AUTHZ_TABLE");
    authz_table_adapter_ = authz_table_adapter.get();
    metric_recorder_ = std::make_unique<MetricRecorder>(
        "p4rt", /*size=*/20, absl::ZeroDuration(),
        std::move(authn_table_adapter), std::move(authz_table_adapter));
    factory_ =
        std::make_unique<AuthzAuditLoggerFactory>(metric_recorder_.get());
    grpc_core::experimental::Json empty_json_config;
    auto config = *factory_->ParseAuditLoggerConfig(empty_json_config);
    logger_ = factory_->CreateAuditLogger(std::move(config));
  }

 protected:
  sonic::FakeSonicDbTable authn_table_;
  sonic::FakeSonicDbTable authz_table_;
  sonic::FakeTableAdapter* authz_table_adapter_;
  std::unique_ptr<MetricRecorder> metric_recorder_;
  std::unique_ptr<AuthzAuditLoggerFactory> factory_;
  std::unique_ptr<grpc::experimental::AuditLogger> logger_;
};

TEST_F(AuthzLoggerTest, AuthzLoggerConfigReportsExpectedValues) {
  grpc_core::experimental::Json json;
  auto config = factory_->ParseAuditLoggerConfig(json).value();
  EXPECT_EQ(config->name(), "authz_logger");
  EXPECT_EQ(config->ToString(), "authz_config");
}

TEST_F(AuthzLoggerTest, AuthzLoggerNameReportsExpectedValues) {
  EXPECT_EQ(logger_->name(), "authz_logger");
}

TEST_F(AuthzLoggerTest, DoesNotRecordInvalidRpc) {
  // The valid RPC method name will look like "/service/rpc_method".
  grpc::experimental::AuditContext context("invalid_rpc", "user", "policy",
                                           "rule", /*authorized=*/true);
  logger_->Log(context);
  context = grpc::experimental::AuditContext("invalid/rpc", "user", "policy",
                                             "rule", /*authorized=*/true);
  logger_->Log(context);
  context = grpc::experimental::AuditContext(
      "//invalid/rpc/rpc", "user", "policy", "rule", /*authorized=*/true);
  logger_->Log(context);
  context = grpc::experimental::AuditContext("//invalid_rpc", "user", "policy",
                                             "rule", /*authorized=*/true);
  logger_->Log(context);
  context = grpc::experimental::AuditContext("/invalid_rpc/", "user", "policy",
                                             "rule", /*authorized=*/true);
  logger_->Log(context);
  absl::SleepFor(absl::Milliseconds(500));

  EXPECT_EQ(authz_table_adapter_->keys().size(), 0);
}

TEST_F(AuthzLoggerTest, PermittedRpcIsLoggedInDb) {
  grpc::experimental::AuditContext context("/service/rpc", "user", "policy",
                                           "rule", /*authorized=*/true);
  logger_->Log(context);

  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|permitted");
      },
      absl::Milliseconds(500)));
  EXPECT_THAT(authz_table_adapter_->get("service|rpc|permitted"),
              Contains(Pair("count", "1")));
}

TEST_F(AuthzLoggerTest, RejectedRpcIsLoggedInDb) {
  grpc::experimental::AuditContext context("/service/rpc", "user", "policy",
                                           "rule", /*authorized=*/false);
  logger_->Log(context);

  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|denied");
      },
      absl::Milliseconds(500)));
  EXPECT_THAT(authz_table_adapter_->get("service|rpc|denied"),
              Contains(Pair("count", "1")));
}

TEST_F(AuthzLoggerTest, MultipleRpcsAreLoggedInDb) {
  grpc::experimental::AuditContext context("/service1/rpc1", "user1", "policy",
                                           "rule", /*authorized=*/true);
  logger_->Log(context);
  logger_->Log(context);
  context = grpc::experimental::AuditContext(
      "/service2/rpc2", "user2", "policy", "rule", /*authorized=*/false);
  logger_->Log(context);
  context = grpc::experimental::AuditContext(
      "/service2/rpc2", "user1", "policy", "rule", /*authorized=*/false);
  logger_->Log(context);
  context = grpc::experimental::AuditContext(
      "/service2/rpc2", "user3", "policy", "rule", /*authorized=*/true);
  logger_->Log(context);
  context = grpc::experimental::AuditContext(
      "/service2/rpc2", "user2", "policy", "rule", /*authorized=*/false);
  logger_->Log(context);

  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service1|rpc1|permitted") &&
               CheckCount(authz_table_adapter_->get("service1|rpc1|permitted"),
                          "2") &&
               authz_table_adapter_->exists("service2|rpc2|permitted") &&
               CheckCount(authz_table_adapter_->get("service2|rpc2|permitted"),
                          "1") &&
               authz_table_adapter_->exists("service2|rpc2|denied") &&
               CheckCount(authz_table_adapter_->get("service2|rpc2|denied"),
                          "3");
      },
      absl::Milliseconds(500)));
}

TEST_F(AuthzLoggerTest, PermittedRpcCounterIncrements) {
  grpc::experimental::AuditContext context("/service/rpc", "user", "policy",
                                           "rule", /*authorized=*/true);

  logger_->Log(context);
  logger_->Log(context);
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|permitted") &&
               CheckCount(authz_table_adapter_->get("service|rpc|permitted"),
                          "2");
      },
      absl::Milliseconds(500)));
  EXPECT_THAT(authz_table_adapter_->get("service|rpc|permitted"),
              Contains(Pair("count", "2")));
}

TEST_F(AuthzLoggerTest, RejectedRpcCounterIncrements) {
  grpc::experimental::AuditContext context("/service/rpc", "user", "policy",
                                           "rule", /*authorized=*/false);
  logger_->Log(context);
  logger_->Log(context);
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|denied") &&
               CheckCount(authz_table_adapter_->get("service|rpc|denied"), "2");
      },
      absl::Milliseconds(500)));
  EXPECT_THAT(authz_table_adapter_->get("service|rpc|denied"),
              Contains(Pair("count", "2")));
}

TEST_F(AuthzLoggerTest, PermittedRpcCounterRecordsLatestTimestamp) {
  grpc::experimental::AuditContext context("/service/rpc", "user", "policy",
                                           "rule", /*authorized=*/true);
  int64_t minimum_timestamp = absl::GetCurrentTimeNanos();
  logger_->Log(context);
  int64_t maximum_timestamp = absl::GetCurrentTimeNanos();
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|permitted");
      },
      absl::Milliseconds(500)));
  EXPECT_THAT(
      authz_table_adapter_->get("service|rpc|permitted"),
      Contains(Pair("timestamp", AllOf(StrAsIntGe(minimum_timestamp),
                                       StrAsIntLe(maximum_timestamp)))));
}

TEST_F(AuthzLoggerTest, RejectedRpcCounterRecordsLatestTimestamp) {
  grpc::experimental::AuditContext context("/service/rpc", "user", "policy",
                                           "rule", /*authorized=*/false);
  int64_t minimum_timestamp = absl::GetCurrentTimeNanos();
  logger_->Log(context);
  int64_t maximum_timestamp = absl::GetCurrentTimeNanos();
  ASSERT_TRUE(WaitUntil(
      [&]() -> bool {
        return authz_table_adapter_->exists("service|rpc|denied");
      },
      absl::Milliseconds(500)));
  EXPECT_THAT(
      authz_table_adapter_->get("service|rpc|denied"),
      Contains(Pair("timestamp", AllOf(StrAsIntGe(minimum_timestamp),
                                       StrAsIntLe(maximum_timestamp)))));
}

}  // namespace
}  // namespace p4rt_app

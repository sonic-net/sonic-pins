// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "lib/validator/validator_backend.h"

#include <string>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace pins_test {
namespace testing {

namespace {

using ::testing::_;
using ::testing::HasSubstr;
using ::testing::MockFunction;
using ::testing::Return;

constexpr int kDefaultRetryCount = 1;
constexpr char kDeviceOne[] = "device_one";
constexpr char kDeviceTwo[] = "device_two";
constexpr char kPingable[] = "Pingable";
constexpr char kSshAble[] = "SshAble";
constexpr char kReady[] = "Ready";
constexpr char kPortsUp[] = "PortsUp";
constexpr absl::Duration kDefaultTime = absl::Minutes(5);

absl::Status CallbackSuccess(absl::string_view, absl::Duration) {
  return absl::OkStatus();
}

absl::Status CallbackError(absl::string_view, absl::Duration) {
  return absl::InternalError("internal error");
}

}  // namespace

class ValidatorBackendTest : public ValidatorBackend {
 public:
  ValidatorBackendTest(absl::flat_hash_set<std::string> devices)
      : ValidatorBackend(devices) {}

  void SetupValidations() override {
    AddCallbacksToValidation(kPingable, {CallbackSuccess});
    AddCallbacksToValidation(kSshAble, {CallbackSuccess});
    AddCallbacksToValidation(kReady, {CallbackSuccess, CallbackError});
  }

  void SetupRetryCallback(absl::string_view validation_tag,
                          const Callback callback) {
    AddCallbacksToValidation(validation_tag, {callback});
  }
};

TEST(ValidatorBackendTest, OneDeviceSuccessTest) {
  ValidatorBackendTest validator_backend_test({kDeviceOne});
  validator_backend_test.SetupValidations();
  EXPECT_OK(validator_backend_test.RunValidations(
      kDeviceOne, {kPingable}, kDefaultRetryCount, kDefaultTime));
}

TEST(ValidatorBackendTest, MultiDevicesSuccessTest) {
  ValidatorBackendTest validator_backend_test({kDeviceOne, kDeviceTwo});
  validator_backend_test.SetupValidations();
  EXPECT_OK(validator_backend_test.RunValidations(
      kDeviceOne, {kPingable}, kDefaultRetryCount, kDefaultTime));
}

TEST(ValidatorBackendTest, InvalidateDeviceIdTest) {
  ValidatorBackendTest validator_backend_test({kDeviceOne});
  validator_backend_test.SetupValidations();
  EXPECT_THAT(validator_backend_test.RunValidations(
                  kDeviceTwo, {kPingable}, kDefaultRetryCount, kDefaultTime),
              gutil::StatusIs(absl::StatusCode::kNotFound,
                              HasSubstr(absl::StrCat(
                                  kDeviceTwo, " not supported by backend"))));
}

TEST(ValidatorBackendTest, InvalidateValidationTest) {
  ValidatorBackendTest validator_backend_test({kDeviceOne});
  validator_backend_test.SetupValidations();
  EXPECT_THAT(
      validator_backend_test.RunValidations(kDeviceOne, {"StackOk"},
                                            kDefaultRetryCount, kDefaultTime),
      gutil::StatusIs(absl::StatusCode::kNotFound,
                      HasSubstr(absl::StrCat(
                          "Validations are not supported by backend."))));
}

TEST(ValidatorBackendTest, MultiValidationsTest) {
  ValidatorBackendTest validator_backend_test({kDeviceOne});
  validator_backend_test.SetupValidations();
  EXPECT_OK(validator_backend_test.RunValidations(
      kDeviceOne, {kPingable, kSshAble}, kDefaultRetryCount, kDefaultTime));
}

TEST(ValidatorBackendTest, MultiDevicesAndValidationsTest) {
  ValidatorBackendTest validator_backend_test({kDeviceOne, kDeviceTwo});
  validator_backend_test.SetupValidations();
  EXPECT_OK(validator_backend_test.RunValidations(
      kDeviceOne, {kPingable}, kDefaultRetryCount, kDefaultTime));
  EXPECT_OK(validator_backend_test.RunValidations(
      kDeviceTwo, {kPingable}, kDefaultRetryCount, kDefaultTime));
}

TEST(ValidatorBackendTest, CallbackFailureTest) {
  ValidatorBackendTest validator_backend_test({kDeviceOne});
  validator_backend_test.SetupValidations();
  EXPECT_THAT(validator_backend_test.RunValidations(
                  kDeviceOne, {kReady}, kDefaultRetryCount, kDefaultTime),
              gutil::StatusIs(
                  absl::StatusCode::kInternal,
                  HasSubstr(absl::StrCat("Running ", kReady, " on ", kDeviceOne,
                                         " fails with internal error after ",
                                         kDefaultRetryCount, " retries"))));
}

TEST(ValidatorBackendTest, RetryFailureTest) {
  MockFunction<absl::Status(absl::string_view, absl::Duration)> retry_mock;
  EXPECT_CALL(retry_mock, Call(_, _))
      .WillOnce(Return(absl::InternalError("internal error")))
      .WillOnce(Return(absl::InternalError("internal error")))
      .WillRepeatedly(Return(absl::OkStatus()));

  ValidatorBackendTest validator_backend_test({kDeviceOne});
  validator_backend_test.SetupRetryCallback(kPortsUp,
                                            retry_mock.AsStdFunction());
  EXPECT_THAT(validator_backend_test.RunValidations(
                  kDeviceOne, {kPortsUp}, kDefaultRetryCount, kDefaultTime),
              gutil::StatusIs(absl::StatusCode::kInternal,
                              HasSubstr(absl::StrCat(
                                  "Running ", kPortsUp, " on ", kDeviceOne,
                                  " fails with internal error after ",
                                  kDefaultRetryCount, " retries"))));
}

TEST(ValidatorBackendTest, RetrySuccessTest) {
  MockFunction<absl::Status(absl::string_view, absl::Duration)> retry_mock;
  EXPECT_CALL(retry_mock, Call(_, _))
      .WillOnce(Return(absl::InternalError("internal error")))
      .WillOnce(Return(absl::InternalError("internal error")))
      .WillRepeatedly(Return(absl::OkStatus()));

  ValidatorBackendTest validator_backend_test({kDeviceOne});
  validator_backend_test.SetupRetryCallback(kPortsUp,
                                            retry_mock.AsStdFunction());
  EXPECT_OK(validator_backend_test.RunValidations(kDeviceOne, {kPortsUp}, 2,
                                                  kDefaultTime));
}

}  // namespace testing
}  // namespace pins_test

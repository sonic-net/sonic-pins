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
#ifndef PINS_TESTS_FORWARDING_ARBITRATION_TEST_H_
#define PINS_TESTS_FORWARDING_ARBITRATION_TEST_H_

#include <cstdint>
#include <memory>
#include <new>
#include <optional>
#include <string>
#include <utility>

#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "grpcpp/grpcpp.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "tests/lib/p4info_helper.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/test_environment.h"

namespace pins {

using ::p4::v1::P4Runtime;

struct ArbitrationTestParams {
  // Using a shared_ptr because parameterized tests require objects to be
  // copyable.
  std::shared_ptr<thinkit::MirrorTestbedInterface> mirror_testbed;
  // The test assumes that the switch is pre-configured if no `gnmi_config` is
  // given (default), or otherwise pushes the given config before starting.
  std::optional<std::string> gnmi_config;
  std::optional<p4::config::v1::P4Info> p4info;
};

class ArbitrationTestFixture
    : public testing::TestWithParam<ArbitrationTestParams> {
public:
  void SetUp() override {
    GetParam().mirror_testbed->SetUp();

    ASSERT_OK_AND_ASSIGN(p4::config::v1::P4Info p4_info,
                         GetP4InfoFromParamOrSUT());

    // Push gnmi configuration / P4Info.
    ASSERT_OK(pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
                  GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                  GetParam().mirror_testbed->GetMirrorTestbed().ControlSwitch(),
                  GetParam().gnmi_config, p4_info)
                  .status());

    device_id_ = GetParam().mirror_testbed->GetMirrorTestbed().Sut().DeviceId();
    //  Sleep for one second, so that we are guaranteed to get a higher
    //  election id than the previous test (we use unix seconds in production
    //  for the upper election id bits, too).
    absl::SleepFor(absl::Seconds(1));
    upper_election_id_ = absl::ToUnixSeconds(absl::Now());
  }

  // TODO: b/361102830 - Support P4 and config restore on teardown.
  void TearDown() override { GetParam().mirror_testbed->TearDown(); }

  // Puts the switch into a known state:
  //  * Forwarding pipeline is configured
  //  * No P4RT entries are programmed.
  absl::Status NormalizeSwitchState(pdpi::P4RuntimeSession *p4rt_session) {
    ASSIGN_OR_RETURN(p4::config::v1::P4Info p4_info, GetP4InfoFromParamOrSUT());
    // Set the forwarding pipeline.
    RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
        p4rt_session,
        p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
        p4_info));

    // Clear entries here in case the previous test did not (e.g. because it
    // crashed).
    RETURN_IF_ERROR(pdpi::ClearTableEntries(p4rt_session));
    // Check that switch is in a clean state.
    ASSIGN_OR_RETURN(auto entries, pdpi::ReadPiTableEntries(p4rt_session));
    if (!entries.empty()) {
      return gutil::FailedPreconditionErrorBuilder()
             << "Read back '" << entries.size()
             << "' entries when all entries should have been cleared.";
    }
    return absl::OkStatus();
  }

  // Returns a P4Runtime stub.
  absl::StatusOr<std::unique_ptr<P4Runtime::StubInterface>> Stub() {
    return GetParam()
        .mirror_testbed->GetMirrorTestbed()
        .Sut()
        .CreateP4RuntimeStub();
  }

  // Makes an election ID given the lower bits. The upper bits are fixed to
  // roughly the current time in seconds, such that we are guaranteed to always
  // get monotonically increasing IDs.
  absl::uint128 ElectionIdFromLower(uint64_t lower_election_id) const {
    return absl::MakeUint128(upper_election_id_, lower_election_id);
  }

  // Attempts to become primary on a given stub.
  absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>>
  BecomePrimary(std::unique_ptr<P4Runtime::StubInterface> stub,
                uint64_t lower_election_id) const {
    return pdpi::P4RuntimeSession::Create(
        std::move(stub), device_id_,
        pdpi::P4RuntimeSessionOptionalArgs{
            .election_id = ElectionIdFromLower(lower_election_id)});
  }

  // Attempts to become primary on a new stub.
  absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>>
  BecomePrimary(uint64_t lower_election_id) {
    ASSIGN_OR_RETURN(auto stub, Stub());
    return BecomePrimary(std::move(stub), lower_election_id);
  }

  uint32_t DeviceId() const { return device_id_; }

  thinkit::TestEnvironment &TestEnvironment() {
    return GetParam().mirror_testbed->GetMirrorTestbed().Environment();
  }

  absl::StatusOr<p4::config::v1::P4Info> GetP4InfoFromParamOrSUT() {
    static const auto *const kP4Info =
        new auto([&]() -> absl::StatusOr<p4::config::v1::P4Info> {
          if (GetParam().p4info.has_value()) {
            return GetParam().p4info.value();
          }
          return pins::GetP4InfoFromSUT(
              GetParam().mirror_testbed->GetMirrorTestbed().Sut());
        }());
    return *kP4Info;
  }

private:
  uint64_t upper_election_id_;
  uint32_t device_id_;
};

} // namespace pins

#endif // PINS_TESTS_FORWARDING_ARBITRATION_TEST_H_

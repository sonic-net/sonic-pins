// Copyright 2025 Google LLC
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
#include "tests/integration/system/nsf/nsf_acl_flow_coverage_test.h"

#include <memory>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"  // NOLINT: Need to add status_matchers.h for using `ASSERT_OK` in upstream code.
#include "gutil/testing.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/integration/system/nsf/interfaces/test_params.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/switch.h"

namespace pins_test {
using ::p4::v1::Entity;
using ::p4::v1::ReadResponse;

// Since the validation is while the traffic is in progress, error margin needs
// to be defined.
constexpr int kErrorPercentage = 1;
constexpr absl::Duration kTrafficRunDuration = absl::Minutes(15);

void NsfAclFlowCoverageTestFixture::SetUp() {
  flow_programmer_ = GetParam().create_flow_programmer();
  traffic_helper_ = GetParam().create_traffic_helper();
  testbed_interface_ = GetParam().create_testbed_interface();
  component_validators_ = GetParam().create_component_validators();
  ssh_client_ = GetParam().create_ssh_client();
  SetupTestbed(testbed_interface_);
  ASSERT_OK_AND_ASSIGN(testbed_, GetTestbed(testbed_interface_));
}
void NsfAclFlowCoverageTestFixture::TearDown() {
  TearDownTestbed(testbed_interface_);
}

namespace {

absl::StatusOr<sai::TableEntries> GetAclFlowEntries() {
  return gutil::ParseProtoOrDie<sai::TableEntries>(
      R"pb(
        entries {
          acl_ingress_table_entry {
            match { ether_type { value: "0x0806" mask: "0xffff" } }
            action { acl_trap { qos_queue: "INBAND_PRIORITY_3" } }
            priority: 2031
          }
        }
        entries {
          acl_ingress_qos_table_entry {
            match { ether_type { value: "0x0806" mask: "0xffff" } }
            action {
              set_qos_queue_and_cancel_copy_above_rate_limit {
                qos_queue: "INBAND_PRIORITY_3"
              }
            }
            priority: 4600
            meter_config { bytes_per_second: 32000 burst_bytes: 8000 }
            controller_metadata: "orion_type: ARP_PUNTFLOW orion_cookie: 9223372036856217610"
          }
        }
      )pb");
}

absl::Status ProgramAclFlows(thinkit::Switch& thinkit_switch,
                             const p4::config::v1::P4Info& p4_info) {
  ASSIGN_OR_RETURN(sai::TableEntries kTableEntries, GetAclFlowEntries());
  ASSIGN_OR_RETURN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt,
                   pdpi::P4RuntimeSession::Create(thinkit_switch));
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::CreateIrP4Info(p4_info));
  std::vector<p4::v1::Entity> pi_entities;
  pi_entities.reserve(kTableEntries.entries_size());
  for (const sai::TableEntry& entry : kTableEntries.entries()) {
    ASSIGN_OR_RETURN(pi_entities.emplace_back(),
                     pdpi::PdTableEntryToPiEntity(ir_p4info, entry));
  }
  LOG(INFO) << "Installing PI table entries on "
            << thinkit_switch.ChassisName();
  return pdpi::InstallPiEntities(sut_p4rt.get(), ir_p4info, pi_entities);
}

}  // namespace

TEST_P(NsfAclFlowCoverageTestFixture, NsfAclFlowCoverageTest) {
  // The test needs at least 1 image_config_param to run.
  if (GetParam().image_config_params.empty()) {
    GTEST_SKIP() << "No image config params provided";
  }
  // Pick the first image config param.
  ImageConfigParams image_config_param = GetParam().image_config_params[0];
  thinkit::Switch& sut = GetSut(testbed_);

  ASSERT_OK(ValidateTestbedState(image_config_param.image_label, testbed_,
                                 *ssh_client_, image_config_param.gnmi_config));
  ASSERT_OK(StoreSutDebugArtifacts(
      absl::StrCat(image_config_param.image_label, "_before_nsf_reboot"),
      testbed_));

  // P4 snapshot before programming flows and starting the traffic.
  LOG(INFO) << "Capturing P4 snapshot before programming flows and starting "
               "the traffic";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot1,
                       TakeP4FlowSnapshot(testbed_));
  ASSERT_OK(SaveP4FlowSnapshot(
      testbed_, p4flow_snapshot1,
      absl::StrCat(sut.ChassisName(),
                   "p4flow_snapshot1_before_programming_flows.txt")));

  // Program all the flows.
  LOG(INFO) << "Programming L3 flows before starting the traffic";
  ASSERT_OK(
      flow_programmer_->ProgramFlows(image_config_param.p4_info, testbed_));
  LOG(INFO) << "Programming ACL flows";
  ASSERT_OK(ProgramAclFlows(sut, image_config_param.p4_info));

  LOG(INFO) << "Starting the traffic";
  ASSERT_OK(traffic_helper_->StartTraffic(testbed_));

  // P4 snapshot before NSF reboot.
  LOG(INFO) << "Capturing P4 snapshot before NSF reboot";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot2,
                       TakeP4FlowSnapshot(testbed_));
  ASSERT_OK(SaveP4FlowSnapshot(
      testbed_, p4flow_snapshot2,
      absl::StrCat(sut.ChassisName(), "p4flow_snapshot2_before_nsf.txt")));

  LOG(INFO) << "Initiating NSF reboot";
  ASSERT_OK(pins_test::NsfReboot(testbed_));
  ASSERT_OK(WaitForNsfReboot(testbed_, *ssh_client_));

  ASSERT_OK(ValidateTestbedState(image_config_param.image_label, testbed_,
                                 *ssh_client_, image_config_param.gnmi_config));
  ASSERT_OK(StoreSutDebugArtifacts(
      absl::StrCat(image_config_param.image_label, "_after_nsf_reboot"),
      testbed_));

  // P4 snapshot after upgrade and NSF reboot.
  LOG(INFO) << "Capturing P4 snapshot after NSF reboot";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot3,
                       TakeP4FlowSnapshot(testbed_));
  ASSERT_OK(SaveP4FlowSnapshot(
      testbed_, p4flow_snapshot3,
      absl::StrCat(sut.ChassisName(), "p4flow_snapshot3_after_nsf.txt")));

  // Stop and validate traffic
  LOG(INFO) << "Stopping the traffic";
  ASSERT_OK(traffic_helper_->StopTraffic(testbed_));

  // TODO: For now, we validate traffic only after stopping
  // traffic. Ideally we would want to validate traffic while injection is in
  // progress to narrow down when the traffic loss occurred (i.e. before
  // reboot, during reboot or after reconciliation).
  LOG(INFO) << "Validating the traffic";
  ASSERT_OK(traffic_helper_->ValidateTraffic(testbed_, kErrorPercentage));

  // Selectively clear flows (eg. not clearing nexthop entries for host
  // testbeds).
  LOG(INFO) << "Clearing the flows";
  ASSERT_OK(flow_programmer_->ClearFlows(testbed_));

  // P4 snapshot after cleaning up flows.
  LOG(INFO) << "Capturing P4 snapshot after cleaning up flows";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot4,
                       TakeP4FlowSnapshot(testbed_));
  ASSERT_OK(SaveP4FlowSnapshot(
      testbed_, p4flow_snapshot4,
      absl::StrCat(sut.ChassisName(),
                   "p4flow_snapshot4_after_clearing_flows.txt")));

  LOG(INFO) << "Comparing P4 snapshots - Before Programming Flows Vs After "
               "Clearing Flows";
  ASSERT_OK(CompareP4FlowSnapshots(p4flow_snapshot1, p4flow_snapshot4));

  LOG(INFO)
      << "Comparing P4 snapshots - Before NSF Reboot Vs. After NSF Reboot";
  ASSERT_OK(CompareP4FlowSnapshots(p4flow_snapshot2, p4flow_snapshot3));
}
}  // namespace pins_test

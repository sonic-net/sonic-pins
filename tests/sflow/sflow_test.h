// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_TESTS_SFLOW_SFLOW_TEST_H_
#define PINS_TESTS_SFLOW_SFLOW_TEST_H_

#include <memory>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gtest/gtest.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/ssh_client.h"

namespace pins {

// The constants structure for NOS
struct NosParameters {
  std::string kRedisExecPrefix;
  std::string kSflowContainerExecPrefix;
  std::string kSudoCmdPrefix;
  bool kIsSwitchLinux;
};

struct SflowTestParams {
  thinkit::GenericTestbedInterface* testbed_interface;
  thinkit::SSHClient* ssh_client;
  std::string gnmi_config;
  p4::config::v1::P4Info p4_info;
  // For sampling size tests.
  int packet_size;
  int sample_size;
  // For sampling rate tests.
  int sample_rate;
  // For NSF tests.
  bool nsf_enabled;
  NosParameters nos_param;
  bool nos_is_sonic;
  bool run_all_tests;
};

// Structure represents a link between SUT and Ixia.
// This is represented by Ixia interface name and the SUT's gNMI interface
// name and its corresponding p4 runtime id.
struct IxiaLink {
  std::string ixia_interface;
  std::string sut_interface;
  int port_id;
};

class SflowTestFixture : public ::testing::TestWithParam<SflowTestParams> {
 protected:
  void SetUp() override;

  void TearDown() override;

  const p4::config::v1::P4Info& GetP4Info() { return GetParam().p4_info; }
  const pdpi::IrP4Info& GetIrP4Info() { return ir_p4_info_; }

  std::unique_ptr<thinkit::GenericTestbed> testbed_;
  pdpi::IrP4Info ir_p4_info_;
  std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub_;
  std::string gnmi_config_with_sflow_;
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session_;
  thinkit::SSHClient* ssh_client_ = GetParam().ssh_client;

  std::vector<IxiaLink> ready_links_;
  // Used for setting gNMI collector config. It would be set to the same as the
  // first collector config port. If config does not have any collector config,
  // it would be set to 6343.
  int collector_port_;
};

class SampleSizeTest : public SflowTestFixture {};

class SampleRateTest : public SflowTestFixture {};

class BackoffTest : public SflowTestFixture {};

class SflowNsfTestFixture : public SflowTestFixture {
  void TearDown() override;
};

struct SflowMirrorTestParams {
  thinkit::MirrorTestbedInterface* testbed_interface;
  thinkit::SSHClient* ssh_client;
  std::string sut_gnmi_config;
  std::string control_gnmi_config;
  p4::config::v1::P4Info sut_p4_info;
  p4::config::v1::P4Info control_p4_info;

  // Used for port breakout test.
  std::string platform_json_path;

  // If enabled, warm reboot would be used in tests instead of cold reboot.
  bool nsf_enabled;

  NosParameters nos_param;
  bool nos_is_sonic;
  bool run_all_tests;
};

struct Port {
  std::string interface_name;
  int port_id;
};

class SflowMirrorTestFixture
    : public ::testing::TestWithParam<SflowMirrorTestParams> {
 protected:
  void SetUp() override;

  void TearDown() override;

  // Issue an NSF reboot request on `test` and wait for gnmi convergence on
  // `gnmi_config`. It would also verify P4 snapshot is the same before and
  // after the reboot.
  absl::Status NsfRebootAndWaitForConvergence(thinkit::MirrorTestbed& testbed,
                                              absl::string_view gnmi_config);

  p4::config::v1::P4Info GetSutP4Info() { return sut_p4_info_; }
  p4::config::v1::P4Info GetControlP4Info() { return control_p4_info_; }
  pdpi::IrP4Info GetSutIrP4Info() { return sut_ir_p4_info_; }
  pdpi::IrP4Info GetControlIrP4Info() { return control_ir_p4_info_; }

  p4::config::v1::P4Info sut_p4_info_, control_p4_info_;
  pdpi::IrP4Info sut_ir_p4_info_, control_ir_p4_info_;
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session_;
  std::unique_ptr<pdpi::P4RuntimeSession> control_p4_session_;
  std::unique_ptr<gnmi::gNMI::StubInterface> sut_gnmi_stub_;
  std::unique_ptr<gnmi::gNMI::StubInterface> control_gnmi_stub_;

  std::string agent_address_;

  // Used for setting gNMI collector config. It would be set to the same as the
  // first collector config port. If config does not have any collector config,
  // it would be set to 6343.
  int collector_port_;
};

class SflowRebootTestFixture : public SflowMirrorTestFixture {};

class SflowPortBreakoutTest : public SflowMirrorTestFixture {};
}  // namespace pins

#endif // PINS_TESTS_SFLOW_SFLOW_TEST_H_

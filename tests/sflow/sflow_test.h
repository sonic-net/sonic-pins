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

#include "gtest/gtest.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins {

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
};

// Structure represents a link between SUT and Ixia.
// This is represented by Ixia interface name and the SUT's gNMI interface
// name and its corrosponding p4 runtime id.
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
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session_;
  thinkit::SSHClient* ssh_client_ = GetParam().ssh_client;

  std::vector<IxiaLink> ready_links_;

 private:
  // Set to true when config already has sampling config and is set to true.
  bool sflow_enabled_by_config_ = false;
};

class SampleSizeTest : public SflowTestFixture {};

class SampleRateTest : public SflowTestFixture {};

struct SflowInbandTestParams {
  thinkit::MirrorTestbedInterface* testbed_interface;
  thinkit::SSHClient* main_ssh_client;
  std::string main_gnmi_config;
  std::string peer_gnmi_config;
  p4::config::v1::P4Info p4_info;
};

struct Port {
  std::string interface_name;
  int port_id;
};

class SflowInbandTestFixture
    : public ::testing::TestWithParam<SflowInbandTestParams> {
 protected:
  void SetUp() override;

  void TearDown() override;
  const p4::config::v1::P4Info& GetP4Info() { return GetParam().p4_info; }
  const pdpi::IrP4Info& GetIrP4Info() { return ir_p4_info_; }
  thinkit::Switch& GetMainSwitch() {
    return GetParam().testbed_interface->GetMirrorTestbed().Sut();
  }
  thinkit::Switch& GetPeerSwitch() {
    return GetParam().testbed_interface->GetMirrorTestbed().ControlSwitch();
  }

  pdpi::IrP4Info ir_p4_info_;
  std::unique_ptr<pdpi::P4RuntimeSession> main_p4_session_;
  std::unique_ptr<pdpi::P4RuntimeSession> peer_p4_session_;
  std::unique_ptr<gnmi::gNMI::StubInterface> peer_gnmi_stub_;

  Port traffic_port_;
  std::string collector_ipv6_;

 private:
  // Set to true when config already has sampling config and is set to true.
  bool sflow_enabled_by_config_ = false;
};
}  // namespace pins

#endif // PINS_TESTS_SFLOW_SFLOW_TEST_H_

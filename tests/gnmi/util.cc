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
#include "tests/gnmi/util.h"

#include <string>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "tests/thinkit_util.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"

namespace pins_test {
namespace {

using ::pins_test::kStateDown;
using ::pins_test::kStateUp;

constexpr absl::Duration kPollingInterval = absl::Seconds(5);
constexpr absl::Duration kPollingTimeout = absl::Minutes(2);

absl::Status CheckSutInterfaceOperStatus(gnmi::gNMI::StubInterface &gnmi_stub,
                                         absl::string_view interface,
                                         OperStatus expected_oper_status) {
  absl::string_view status =
      (expected_oper_status == OperStatus::kUp) ? kStateUp : kStateDown;

  absl::StatusOr<OperStatus> actual_oper_status;
  // Polling for 2 minutes.
  const absl::Time polling_end_time = absl::Now() + kPollingTimeout;
  do {
    actual_oper_status = GetInterfaceOperStatusOverGnmi(gnmi_stub, interface);
    if (actual_oper_status.ok() &&
        *actual_oper_status == expected_oper_status) {
      return absl::OkStatus();
    }
    absl::SleepFor(kPollingInterval);
  } while (absl::Now() < polling_end_time);

  if (!actual_oper_status.ok()) {
    return gutil::InternalErrorBuilder()
           << "Failed to get Oper Status of interface "
           << interface << ". Expected: " << status
           << " Actual: " << actual_oper_status.status();
  }

  if (*actual_oper_status != expected_oper_status) {
    return gutil::InternalErrorBuilder()
           << "Mismatch in Oper Status of interface "
           << interface << ". Expected: " << status;
  }
  return absl::OkStatus();
}

absl::Status
CheckControlDeviceInterfaceLinkState(thinkit::GenericTestbed &generic_testbed,
                                     std::string interface, bool is_link_up,
                                     int peer_device_index) {
  ASSIGN_OR_RETURN(
      auto up_links,
      generic_testbed.ControlDevice(peer_device_index).GetUpLinks({interface}));
  if (up_links.empty() == is_link_up) {
    return gutil::InternalErrorBuilder()
           << "Mismatch in Link Up State of interface "
           << interface << ". Expected: " << is_link_up
           << " Actual: " << up_links.empty();
  }
  return absl::OkStatus();
}

}  // namespace

absl::Status SetAdminStatus(gnmi::gNMI::StubInterface* gnmi_stub,
                            absl::string_view if_name,
                            absl::string_view if_status,
                            absl::Duration timeout) {
  std::string enable_status;
  if (if_status == "UP") {
    enable_status = kEnabledTrue;
  } else if (if_status == "DOWN") {
    enable_status = kEnabledFalse;
  } else {
    return absl::InvalidArgumentError("Interface status invalid.");
  }

  // Enable/Disable front panel port.
  LOG(INFO) << "Set front panel port " << if_name << " status: " << if_status;
  const std::string if_enabled_config_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/config/enabled");
  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(
      gnmi_stub, if_enabled_config_path, GnmiSetType::kUpdate, enable_status));
  absl::SleepFor(timeout);

  // Verifies /interfaces/interface[name=<port>]/state/admin-status = UP/DOWN.
  std::string if_state_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/state");
  std::string resp_parse_str = "openconfig-interfaces:state";
  ASSIGN_OR_RETURN(
      std::string state_path_response,
      GetGnmiStatePathInfo(gnmi_stub, if_state_path, resp_parse_str));
  if (!absl::StrContains(state_path_response, if_status)) {
    return absl::InternalError(
        absl::StrCat("Unable to set admin status: ", if_status));
  }
  return absl::OkStatus();
}

absl::Status FlapLink(gnmi::gNMI::StubInterface &gnmi_stub,
                      thinkit::GenericTestbed &generic_testbed,
                      absl::string_view sut_interface,
                      const thinkit::InterfaceInfo& host_interface_info,
                      bool is_ixia_testbed) {
  // Check if both SUT and Peer interfaces are up.
  LOG(INFO) << "Validate SUT interface " << sut_interface
            << " state before bringing down the SUT interface";
  RETURN_IF_ERROR(
      CheckSutInterfaceOperStatus(gnmi_stub, sut_interface, OperStatus::kUp));

  if (!is_ixia_testbed) {
    LOG(INFO) << "Validate Peer interface "
              << host_interface_info.peer_interface_name
              << " state before bringing down the SUT interface";
    RETURN_IF_ERROR(CheckControlDeviceInterfaceLinkState(
        generic_testbed, host_interface_info.peer_interface_name,
        /*is_link_up=*/true, host_interface_info.peer_device_index));
  }
  // Sets admin-status Down through gNMI.
  LOG(INFO) << "Set SUT interface: " << sut_interface
            << " admin link state down.";
  RETURN_IF_ERROR(SetAdminStatus(&gnmi_stub, sut_interface, "DOWN"));
  LOG(INFO) << "Validate SUT interface: " << sut_interface
            << " state after bringing down the SUT interface";
  RETURN_IF_ERROR(
      CheckSutInterfaceOperStatus(gnmi_stub, sut_interface, OperStatus::kDown));
  // Sets admin-status Up through gNMI.
  LOG(INFO) << "Set SUT interface: " << sut_interface
            << " admin link state up.";
  RETURN_IF_ERROR(SetAdminStatus(&gnmi_stub, sut_interface, "UP"));
  LOG(INFO) << "Validate SUT interface: " << sut_interface
            << " state after bringing up the SUT interface";
  RETURN_IF_ERROR(
      CheckSutInterfaceOperStatus(gnmi_stub, sut_interface, OperStatus::kUp));

  // Return early for IXIA testbed as we cannot flap/validate the link on
  // the IXIA end.
  if (is_ixia_testbed) return absl::OkStatus();

  LOG(INFO) << "Validate Peer interface: "
            << host_interface_info.peer_interface_name
            << " state after bringing up the SUT interface";
  RETURN_IF_ERROR(CheckControlDeviceInterfaceLinkState(
      generic_testbed, host_interface_info.peer_interface_name,
      /*is_link_up=*/true, host_interface_info.peer_device_index));

  // flapping child interfaces on the host side.
  if (absl::StartsWith(host_interface_info.peer_interface_name, "eth")) {
    LOG(WARNING) << "Skipping link flap for control device with interface name "
                 << host_interface_info.peer_interface_name
                 << " since SetAdminLinkState() is not implemented.";
    return absl::OkStatus();
  }
  // Flaps control device port and checks that SUT’s gNMI reflects that.
  LOG(INFO) << "Set Peer interface: " << host_interface_info.peer_interface_name
            << " admin link state down.";
  absl::Status control_status =
      generic_testbed.ControlDevice().SetAdminLinkState(
          {host_interface_info.peer_interface_name}, thinkit::LinkState::kDown);

  if (absl::IsUnimplemented(control_status)) {
    LOG(WARNING) << "Skipping link flap for control device since "
                    "SetAdminLinkState() is not implemented.";
    return absl::OkStatus();
  }

  RETURN_IF_ERROR(control_status);
  // Checks oper-status through gNMI.
  LOG(INFO) << "Validate SUT interface: " << sut_interface
            << " state after bringing down the Peer interface";
  RETURN_IF_ERROR(
      CheckSutInterfaceOperStatus(gnmi_stub, sut_interface, OperStatus::kDown));
  LOG(INFO) << "Set Peer interface: " << host_interface_info.peer_interface_name
            << " admin link state up.";
  RETURN_IF_ERROR(generic_testbed.ControlDevice().SetAdminLinkState(
      {host_interface_info.peer_interface_name}, thinkit::LinkState::kUp));
  LOG(INFO) << "Validate SUT interface: " << sut_interface
            << " state after bringing up the Peer interface";
  return CheckSutInterfaceOperStatus(gnmi_stub, sut_interface, OperStatus::kUp);
}

}  // namespace pins_test

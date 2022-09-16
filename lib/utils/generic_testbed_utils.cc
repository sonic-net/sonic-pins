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

#include "lib/utils/generic_testbed_utils.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/validator/validator_lib.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {

std::vector<std::string> GetSutInterfaces(
    absl::Span<const InterfaceLink> links) {
  std::vector<std::string> interfaces;
  interfaces.reserve(links.size());
  for (const InterfaceLink& link : links) {
    interfaces.push_back(link.sut_interface);
  }
  return interfaces;
}

std::vector<std::string> GetPeerInterfaces(
    absl::Span<const InterfaceLink> links) {
  std::vector<std::string> interfaces;
  interfaces.reserve(links.size());
  for (const InterfaceLink& link : links) {
    interfaces.push_back(link.peer_interface);
  }
  return interfaces;
}

std::vector<InterfaceLink> GetAllControlLinks(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info) {
  std::vector<InterfaceLink> links;
  for (const auto& [sut_interface, interface_info] : sut_interface_info) {
    if (interface_info.interface_mode ==
        thinkit::InterfaceMode::CONTROL_INTERFACE) {
      links.push_back(
          InterfaceLink{.sut_interface = sut_interface,
                        .peer_interface = interface_info.peer_interface_name});
    }
  }
  return links;
}

std::vector<InterfaceLink> GetAllTrafficGeneratorLinks(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info) {
  std::vector<InterfaceLink> links;
  for (const auto& [sut_interface, interface_info] : sut_interface_info) {
    if (interface_info.interface_mode ==
        thinkit::InterfaceMode::TRAFFIC_GENERATOR) {
      links.push_back(
          InterfaceLink{.sut_interface = sut_interface,
                        .peer_interface = interface_info.peer_interface_name});
    }
  }
  return links;
}

std::vector<std::string> GetAllLoopbackInterfaces(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info) {
  std::vector<std::string> interfaces;
  for (const auto& [sut_interface, interface_info] : sut_interface_info) {
    if (interface_info.interface_mode == thinkit::InterfaceMode::LOOPBACK) {
      interfaces.push_back(sut_interface);
    }
  }
  return interfaces;
}

std::vector<std::string> GetAllConnectedInterfaces(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info) {
  std::vector<std::string> interfaces;
  for (const auto& [sut_interface, interface_info] : sut_interface_info) {
    if (interface_info.interface_mode != thinkit::InterfaceMode::DISCONNECTED) {
      interfaces.push_back(sut_interface);
    }
  }
  return interfaces;
}

absl::StatusOr<std::vector<std::string>> GetUpInterfaces(
    decltype(GetAllConnectedInterfaces) get_interfaces,
    thinkit::GenericTestbed& testbed) {
  ASSIGN_OR_RETURN(auto gnmi_stub, testbed.Sut().CreateGnmiStub());

  std::vector<std::string> up_interfaces;
  for (std::string& interface : FromTestbed(get_interfaces, testbed)) {
    ASSIGN_OR_RETURN(OperStatus oper_status,
                     GetInterfaceOperStatusOverGnmi(*gnmi_stub, interface));
    if (oper_status != OperStatus::kUp) {
      continue;
    }
    up_interfaces.push_back(std::move(interface));
  }
  return up_interfaces;
}

absl::StatusOr<std::vector<InterfaceLink>> GetUpLinks(
    decltype(GetAllControlLinks) get_links, thinkit::GenericTestbed& testbed) {
  ASSIGN_OR_RETURN(auto gnmi_stub, testbed.Sut().CreateGnmiStub());

  std::vector<InterfaceLink> up_links;
  for (InterfaceLink& link : FromTestbed(get_links, testbed)) {
    ASSIGN_OR_RETURN(
        OperStatus oper_status,
        GetInterfaceOperStatusOverGnmi(*gnmi_stub, link.sut_interface));
    if (oper_status != OperStatus::kUp) {
      continue;
    }
    up_links.push_back(std::move(link));
  }
  return up_links;
}

absl::Status ValidateTestbedPortsUp(thinkit::GenericTestbed& testbed) {
  auto sut_status =
      PortsUp(testbed.Sut(), FromTestbed(GetAllConnectedInterfaces, testbed));
  auto control_interfaces =
      GetPeerInterfaces(FromTestbed(GetAllControlLinks, testbed));
  absl::Status control_status =
      testbed.ControlDevice().ValidatePortsUp(control_interfaces);

  RETURN_IF_ERROR(sut_status);
  return control_status;
}
}  // namespace pins_test

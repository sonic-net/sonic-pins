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

#include "lib/pins_control_device.h"

#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "diag/diag.grpc.pb.h"
#include "diag/diag.pb.h"
#include "glog/logging.h"
#include "grpcpp/client_context.h"
#include "grpcpp/impl/codegen/client_context.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_programming_context.h"
#include "lib/p4rt/packet_listener.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "system/system.grpc.pb.h"
#include "system/system.pb.h"
#include "tests/forwarding/util.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/control_device.h"
#include "thinkit/packet_generation_finalizer.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

constexpr char kIfEnabledConfigPath[] =
    R"(interfaces/interface[name=$0]/config/enabled)";
constexpr char kInterfaceStatePath[] =
    R"(interfaces/interface[name=$0]/state$1)";
constexpr char kIfEnableConfig[] = R"({"enabled":$0})";

absl::StatusOr<gnmi::SetRequest> BuildGnmiSetLinkStateRequest(
    absl::string_view interface, thinkit::LinkState state) {
  switch (state) {
    case thinkit::LinkState::kUp:
      return pins_test::BuildGnmiSetRequest(
          absl::Substitute(kIfEnabledConfigPath, interface),
          pins_test::GnmiSetType::kUpdate,
          absl::Substitute(kIfEnableConfig, "true"));
    case thinkit::LinkState::kDown:
      return pins_test::BuildGnmiSetRequest(
          absl::Substitute(kIfEnabledConfigPath, interface),
          pins_test::GnmiSetType::kUpdate,
          absl::Substitute(kIfEnableConfig, "false"));
    case thinkit::LinkState::kUnknown:
      return absl::InvalidArgumentError("Invalid link state: Unknown");
    default:
      return absl::InvalidArgumentError("Invalid link state.");
  }
}

}  // namespace

PinsControlDevice::PinsControlDevice(
    std::unique_ptr<thinkit::Switch> sut, pdpi::IrP4Info ir_p4_info,
    std::unique_ptr<pdpi::P4RuntimeSession> control_session,
    absl::flat_hash_map<std::string, std::string> interface_name_to_port_id)
    : sut_(std::move(sut)),
      ir_p4_info_(std::move(ir_p4_info)),
      control_session_(std::move(control_session)),
      interface_name_to_port_id_(std::move(interface_name_to_port_id)) {
  for (const auto& [name, port_id] : interface_name_to_port_id_) {
    interface_port_id_to_name_[port_id] = name;
  }
}

absl::StatusOr<PinsControlDevice> PinsControlDevice::Create(
    std::unique_ptr<thinkit::Switch> sut, p4::config::v1::P4Info p4_info) {
  ASSIGN_OR_RETURN(auto gnmi_stub, sut->CreateGnmiStub());
  ASSIGN_OR_RETURN(auto interface_name_to_port_id,
                   GetAllInterfaceNameToPortId(*gnmi_stub));
  ASSIGN_OR_RETURN(auto ir_p4_info, pdpi::CreateIrP4Info(p4_info));
  ASSIGN_OR_RETURN(auto control_session,
                   pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                       *sut, /*gnmi_config=*/std::nullopt, std::move(p4_info)));
  return PinsControlDevice(std::move(sut), std::move(ir_p4_info),
                           std::move(control_session),
                           std::move(interface_name_to_port_id));
}

absl::StatusOr<std::unique_ptr<thinkit::PacketGenerationFinalizer>>
PinsControlDevice::CollectPackets() {
  if (control_session_ == nullptr) {
    return absl::InternalError(
        "No P4RuntimeSession exists; Likely failed to establish another "
        "P4RuntimeSession.");
  }

  // Program the punt all table entry through the context, which will remove
  // this flow once packet collection has finished.
  P4rtProgrammingContext context(control_session_.get());
  ASSIGN_OR_RETURN(
      p4::v1::WriteRequest punt_all_request,
      pdpi::PdWriteRequestToPi(
          ir_p4_info_,
          gutil::ParseProtoOrDie<sai::WriteRequest>(
              R"pb(
                updates {
                  type: INSERT
                  table_entry {
                    acl_ingress_table_entry {
                      match {}                                  # Wildcard match.
                      action { acl_trap { qos_queue: "0x7" } }  # Action: punt.
                      priority: 1                               # Highest priority.
                    }
                  }
                })pb")));
  RETURN_IF_ERROR(context.SendWriteRequest(punt_all_request));

  return absl::make_unique<PacketListener>(
      control_session_.get(), std::move(context),
      sai::Instantiation::kMiddleblock, &interface_port_id_to_name_);
}

absl::StatusOr<std::string> PinsControlDevice::RunCommand(
    absl::string_view command, absl::Duration timeout) {
  return absl::UnimplementedError(
      "RunCommand is not supported by PinsControlDevice.");
}

absl::Status PinsControlDevice::SendPacket(
    absl::string_view interface, absl::string_view packet,
    std::optional<absl::Duration> packet_delay) {
  if (control_session_ == nullptr) {
    return absl::InternalError(
        "No P4RuntimeSession exists; Likely failed to establish another "
        "P4RuntimeSession.");
  }
  return pins::InjectEgressPacket(interface_name_to_port_id_[interface],
                                   std::string(packet), ir_p4_info_,
                                   control_session_.get(), packet_delay);
}

absl::Status PinsControlDevice::SendPackets(
    absl::string_view interface, absl::Span<const std::string> packets) {
  for (absl::string_view packet : packets) {
    RETURN_IF_ERROR(SendPacket(interface, packet, std::nullopt));
  }
  return absl::OkStatus();
}

absl::Status PinsControlDevice::SetAdminLinkState(
    absl::Span<const std::string> interfaces, thinkit::LinkState state) {
  ASSIGN_OR_RETURN(auto gnmi_stub, sut_->CreateGnmiStub());
  gnmi::SetResponse response;
  for (const std::string& interface : interfaces) {
    grpc::ClientContext context;
    ASSIGN_OR_RETURN(gnmi::SetRequest gnmi_set_request,
                     BuildGnmiSetLinkStateRequest(interface, state));
    LOG(INFO) << "Sending gNMI set admin link state request: "
              << gnmi_set_request.ShortDebugString();
    RETURN_IF_ERROR(gutil::GrpcStatusToAbslStatus(
        gnmi_stub->Set(&context, gnmi_set_request, &response)));
  }
  return absl::OkStatus();
}

absl::Status PinsControlDevice::Reboot(thinkit::RebootType reboot_type) {
  ASSIGN_OR_RETURN(auto gnoi_system_stub, sut_->CreateGnoiSystemStub());
  gnoi::system::RebootRequest request;
  if (reboot_type == thinkit::RebootType::kCold) {
    request.set_method(gnoi::system::RebootMethod::COLD);
  } else if (reboot_type == thinkit::RebootType::kWarm) {
    request.set_method(gnoi::system::RebootMethod::WARM);
  } else {
    request.set_method(gnoi::system::RebootMethod::UNKNOWN);
  }
  request.set_message("Testing Purpose");
  gnoi::system::RebootResponse response;
  grpc::ClientContext context;
  LOG(INFO) << "Sending gNOI reboot request: " << request.ShortDebugString();
  return gutil::GrpcStatusToAbslStatus(
      gnoi_system_stub->Reboot(&context, request, &response));
}

absl::StatusOr<gnoi::diag::StartBERTResponse> PinsControlDevice::StartBERT(
    const gnoi::diag::StartBERTRequest& request) {
  ASSIGN_OR_RETURN(auto gnoi_diag_stub, sut_->CreateGnoiDiagStub());
  gnoi::diag::StartBERTResponse response;
  grpc::ClientContext context;
  LOG(INFO) << "Sending StartBERT request: " << request.ShortDebugString();
  absl::Status status = gutil::GrpcStatusToAbslStatus(
      gnoi_diag_stub->StartBERT(&context, request, &response));
  if (!status.ok()) {
    LOG(INFO) << "Failed to start BERT request.";
    return status;
  }
  return response;
}

absl::StatusOr<gnoi::diag::StopBERTResponse> PinsControlDevice::StopBERT(
    const gnoi::diag::StopBERTRequest& request) {
  ASSIGN_OR_RETURN(auto gnoi_diag_stub, sut_->CreateGnoiDiagStub());
  gnoi::diag::StopBERTResponse response;
  grpc::ClientContext context;
  LOG(INFO) << "Sending StopBERT request: " << request.ShortDebugString();
  absl::Status status = gutil::GrpcStatusToAbslStatus(
      gnoi_diag_stub->StopBERT(&context, request, &response));
  if (!status.ok()) {
    LOG(INFO) << "Failed to stop BERT request.";
    return status;
  }
  return response;
}

absl::StatusOr<gnoi::diag::GetBERTResultResponse>
PinsControlDevice::GetBERTResult(
    const gnoi::diag::GetBERTResultRequest& request) {
  ASSIGN_OR_RETURN(auto gnoi_diag_stub, sut_->CreateGnoiDiagStub());
  gnoi::diag::GetBERTResultResponse response;
  grpc::ClientContext context;
  LOG(INFO) << "Sending get BERT result request: "
            << request.ShortDebugString();
  absl::Status status = gutil::GrpcStatusToAbslStatus(
      gnoi_diag_stub->GetBERTResult(&context, request, &response));
  if (!status.ok()) {
    LOG(INFO) << "Failed to get BERT result request.";
    return status;
  }
  return response;
}

absl::StatusOr<absl::flat_hash_set<std::string>> PinsControlDevice::GetUpLinks(
    absl::Span<const std::string> interfaces) {
  ASSIGN_OR_RETURN(auto gnmi_stub, sut_->CreateGnmiStub());
  gnmi::GetResponse response;
  absl::flat_hash_set<std::string> up_links;
  for (const std::string& interface : interfaces) {
    grpc::ClientContext context;
    ASSIGN_OR_RETURN(std::string admin_status_response,
                     GetGnmiStatePathInfo(
                         gnmi_stub.get(),
                         absl::Substitute(kInterfaceStatePath, interface, ""),
                         "openconfig-interfaces:state"));
    if (absl::StrContains(admin_status_response, "\"oper-status\":\"UP\""))
      up_links.insert(interface);
  }
  return up_links;
}

absl::Status PinsControlDevice::CheckUp() { return SwitchReady(*sut_); }

absl::Status PinsControlDevice::ValidatePortsUp(
    absl::Span<const std::string> interfaces) {
      return PortsUp(*sut_, interfaces);
}

absl::Status PinsControlDevice::FlapLinks(const absl::string_view interface,
                                          const absl::Duration down_duration) {
  return absl::UnimplementedError(
      "FlapLinks is not supported by PinsControlDevice.");
}

absl::StatusOr<absl::flat_hash_map<std::string, int>>
PinsControlDevice::GetInterfaceLaneSpeed(
     absl::flat_hash_set<std::string>& interfaces) {
  ASSIGN_OR_RETURN(auto gnmi_stub, sut_->CreateGnmiStub());
  return pins_test::GetInterfaceToLaneSpeedMap(*gnmi_stub, interfaces);
}

absl::StatusOr<std::vector<std::string>>
PinsControlDevice::FilterCollateralDownOnAdminDownInterfaces(
    absl::Span<const std::string> interfaces) {
  return std::vector<std::string>(interfaces.begin(), interfaces.end());
}

}  // namespace pins_test

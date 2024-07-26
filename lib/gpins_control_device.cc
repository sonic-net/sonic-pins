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

#include "lib/gpins_control_device.h"

#include <memory>
#include <string>
#include <utility>

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
#include "gutil/status.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/packet_listener.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "include/nlohmann/json.hpp"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "system/system.grpc.pb.h"
#include "system/system.pb.h"
#include "tests/forwarding/util.h"
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

GpinsControlDevice::GpinsControlDevice(
    std::unique_ptr<thinkit::Switch> sut,
    std::unique_ptr<pdpi::P4RuntimeSession> control_p4_session,
    pdpi::IrP4Info ir_p4info,
    absl::flat_hash_map<std::string, std::string> interface_name_to_port_id)
    : sut_(std::move(sut)),
      control_p4_session_(std::move(control_p4_session)),
      ir_p4info_(std::move(ir_p4info)),
      interface_name_to_port_id_(std::move(interface_name_to_port_id)) {
  for (const auto& [name, port_id] : interface_name_to_port_id_) {
    interface_port_id_to_name_[port_id] = name;
  }
}

absl::StatusOr<GpinsControlDevice> GpinsControlDevice::CreateGpinsControlDevice(
    std::unique_ptr<thinkit::Switch> sut) {
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));

  // Adds PacketIO rule
  ASSIGN_OR_RETURN(
      auto control_p4_session,
      pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(*sut, p4info));
  ASSIGN_OR_RETURN(auto gnmi_stub, sut->CreateGnmiStub());
  ASSIGN_OR_RETURN(auto interface_name_to_port_id,
                   GetAllInterfaceNameToPortId(*gnmi_stub));
  return GpinsControlDevice(std::move(sut), std::move(control_p4_session),
                            std::move(ir_p4info),
                            std::move(interface_name_to_port_id));
}

absl::StatusOr<std::unique_ptr<thinkit::PacketGenerationFinalizer>>
GpinsControlDevice::CollectPackets(thinkit::PacketCallback callback) {
  return absl::make_unique<PacketListener>(
      control_p4_session_.get(), &ir_p4info_, &interface_port_id_to_name_,
      callback);
}

absl::Status GpinsControlDevice::SendPacket(absl::string_view interface,
                                            absl::string_view packet) {
  return gpins::InjectEgressPacket(interface_name_to_port_id_[interface],
                                   std::string(packet), ir_p4info_,
                                   control_p4_session_.get());
}

absl::Status GpinsControlDevice::SendPackets(
    absl::string_view interface, absl::Span<const std::string> packets) {
  for (absl::string_view packet : packets) {
    RETURN_IF_ERROR(SendPacket(interface, packet));
  }
  return absl::OkStatus();
}

absl::Status GpinsControlDevice::SetAdminLinkState(
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

absl::Status GpinsControlDevice::Reboot(thinkit::RebootType reboot_type) {
  ASSIGN_OR_RETURN(auto gnoi_system_stub, sut_->CreateGnoiSystemStub());
  gnoi::system::RebootRequest request;
  if (reboot_type == thinkit::RebootType::kCold) {
    request.set_method(gnoi::system::RebootMethod::COLD);
    request.set_delay(absl::ToInt64Nanoseconds(absl::Seconds(1)));
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

absl::StatusOr<gnoi::diag::StartBERTResponse> GpinsControlDevice::StartBERT(
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

absl::StatusOr<gnoi::diag::StopBERTResponse> GpinsControlDevice::StopBERT(
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
GpinsControlDevice::GetBERTResult(
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

absl::StatusOr<absl::flat_hash_set<std::string>> GpinsControlDevice::GetUpLinks(
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

absl::Status GpinsControlDevice::CheckUp() { return SwitchReady(*sut_); }

}  // namespace pins_test

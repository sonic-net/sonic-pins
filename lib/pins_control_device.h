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

#ifndef PINS_LIB_PINS_CONTROL_DEVICE_H_
#define PINS_LIB_PINS_CONTROL_DEVICE_H_

#include <memory>
#include <optional>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "diag/diag.grpc.pb.h"
#include "diag/diag.pb.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "system/system.grpc.pb.h"
#include "thinkit/control_device.h"
#include "thinkit/packet_generation_finalizer.h"
#include "thinkit/switch.h"

namespace pins_test {

// A `PinsControlDevice` represents a single PINs switch used as a control
// device for a ThinKit generic testbed.
class PinsControlDevice : public thinkit::ControlDevice {
public:
  static absl::StatusOr<PinsControlDevice>
  Create(std::unique_ptr<thinkit::Switch> sut,
         p4::config::v1::P4Info p4_info =
             sai::GetP4Info(sai::Instantiation::kMiddleblock));

  PinsControlDevice(
      std::unique_ptr<thinkit::Switch> sut, pdpi::IrP4Info ir_p4_info,
      std::unique_ptr<pdpi::P4RuntimeSession> control_session,
      absl::flat_hash_map<std::string, std::string> interface_name_to_port_id);

  absl::StatusOr<std::unique_ptr<thinkit::PacketGenerationFinalizer>>
  CollectPackets() override;

  absl::StatusOr<std::string> RunCommand(absl::string_view command,
                                         absl::Duration timeout) override;

  absl::Status SendPacket(absl::string_view interface, absl::string_view packet,
                          std::optional<absl::Duration> packet_delay) override;

  bool SupportsSendPacket() const override { return true; }

  absl::Status SendPackets(absl::string_view interface,
                           absl::Span<const std::string> packets) override;

  absl::Status SetAdminLinkState(absl::Span<const std::string> interfaces,
                                 thinkit::LinkState state) override;

  absl::Status Reboot(thinkit::RebootType reboot_type) override;

  absl::StatusOr<::gnoi::diag::StartBERTResponse>
  StartBERT(const ::gnoi::diag::StartBERTRequest &request) override;

  absl::StatusOr<::gnoi::diag::StopBERTResponse>
  StopBERT(const ::gnoi::diag::StopBERTRequest &request) override;

  absl::StatusOr<::gnoi::diag::GetBERTResultResponse>
  GetBERTResult(const ::gnoi::diag::GetBERTResultRequest &request) override;

  absl::StatusOr<absl::flat_hash_set<std::string>>
  GetUpLinks(absl::Span<const std::string> interfaces) override;

  absl::Status CheckUp() override;

  absl::Status
  ValidatePortsUp(absl::Span<const std::string> interfaces) override;

  absl::Status FlapLinks(absl::string_view interface,
                         absl::Duration down_duration) override;

  absl::StatusOr<absl::flat_hash_map<std::string, int>>
  GetInterfaceLaneSpeed(absl::flat_hash_set<std::string> &interfaces) override;

  absl::StatusOr<std::vector<std::string>>
  FilterCollateralDownOnAdminDownInterfaces(
      absl::Span<const std::string> interfaces) override;

private:
  std::unique_ptr<thinkit::Switch> sut_;
  pdpi::IrP4Info ir_p4_info_;
  std::unique_ptr<pdpi::P4RuntimeSession> control_session_;
  absl::flat_hash_map<std::string, std::string> interface_name_to_port_id_;
  absl::flat_hash_map<std::string, std::string> interface_port_id_to_name_;
};

} // namespace pins_test

#endif // PINS_LIB_PINS_CONTROL_DEVICE_H_

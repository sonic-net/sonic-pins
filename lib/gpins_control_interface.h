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

#ifndef GOOGLE_LIB_GPINS_CONTROL_INTERFACE_H_
#define GOOGLE_LIB_GPINS_CONTROL_INTERFACE_H_

#include <memory>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "diag/diag.grpc.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "system/system.grpc.pb.h"
#include "thinkit/control_interface.h"
#include "thinkit/packet_generation_finalizer.h"
#include "thinkit/switch.h"

namespace pins_test {

class GpinsControlInterface : public thinkit::ControlInterface {
 public:
  static absl::StatusOr<GpinsControlInterface> CreateGpinsControlInterface(
      std::unique_ptr<thinkit::Switch> sut);

  GpinsControlInterface(
      std::unique_ptr<thinkit::Switch> sut,
      std::unique_ptr<pdpi::P4RuntimeSession> control_p4_session,
      pdpi::IrP4Info ir_p4info,
      absl::flat_hash_map<std::string, std::string> interface_name_to_port_id);

  absl::StatusOr<std::unique_ptr<thinkit::PacketGenerationFinalizer>>
  CollectPackets(thinkit::PacketCallback callback) override;

  absl::Status SendPacket(absl::string_view interface,
                          absl::string_view packet) override;

  absl::Status SendPackets(absl::string_view interface,
                           absl::Span<const std::string> packets) override;

  absl::Status SetAdminLinkState(absl::Span<const std::string> interfaces,
                                 thinkit::LinkState state) override;

  absl::Status Reboot(thinkit::RebootType reboot_type) override;

  absl::StatusOr<::gnoi::diag::StartBERTResponse> StartBERT(
      const ::gnoi::diag::StartBERTRequest& request) override;

  absl::StatusOr<::gnoi::diag::StopBERTResponse> StopBERT(
      const ::gnoi::diag::StopBERTRequest& request) override;

  absl::StatusOr<::gnoi::diag::GetBERTResultResponse> GetBERTResult(
      const ::gnoi::diag::GetBERTResultRequest& request) override;

  absl::StatusOr<absl::flat_hash_set<std::string>> GetUpLinks(
      absl::Span<const std::string> interfaces) override;

  absl::Status CheckUp() override;

 private:
  std::unique_ptr<thinkit::Switch> sut_;
  std::unique_ptr<pdpi::P4RuntimeSession> control_p4_session_;
  pdpi::IrP4Info ir_p4info_;
  absl::flat_hash_map<std::string, std::string> interface_name_to_port_id_;
  absl::flat_hash_map<std::string, std::string> interface_port_id_to_name_;
};

}  // namespace pins_test

#endif  // GOOGLE_LIB_GPINS_CONTROL_INTERFACE_H_

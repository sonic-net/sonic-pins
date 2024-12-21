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

#ifndef PINS_THINKIT_MOCK_CONTROL_DEVICE_H_
#define PINS_THINKIT_MOCK_CONTROL_DEVICE_H_

#include <memory>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "diag/diag.grpc.pb.h"
#include "diag/diag.pb.h"
#include "thinkit/control_device.h"
#include "thinkit/packet_generation_finalizer.h"
#include "gmock/gmock.h"

namespace thinkit {

class MockControlDevice : public ControlDevice {
public:
  MOCK_METHOD(
      absl::StatusOr<std::unique_ptr<thinkit::PacketGenerationFinalizer>>,
      CollectPackets, (), (override));
  MOCK_METHOD(absl::Status, SendPacket,
              (absl::string_view interface, absl::string_view packet,
               std::optional<absl::Duration> packet_delay),
              (override));
  MOCK_METHOD(bool, SupportsSendPacket, (), (const, override));
  MOCK_METHOD(absl::Status, SendPackets,
              (absl::string_view interface,
               absl::Span<const std::string> packets),
              (override));
  MOCK_METHOD(absl::Status, SetAdminLinkState,
              (absl::Span<const std::string> sut_ports, LinkState state),
              (override));
  MOCK_METHOD(absl::Status, Reboot, (RebootType reboot_Type), (override));
  MOCK_METHOD(absl::StatusOr<gnoi::diag::StartBERTResponse>, StartBERT,
              (const gnoi::diag::StartBERTRequest &request), (override));
  MOCK_METHOD(absl::StatusOr<gnoi::diag::StopBERTResponse>, StopBERT,
              (const gnoi::diag::StopBERTRequest &request), (override));
  MOCK_METHOD(absl::StatusOr<gnoi::diag::GetBERTResultResponse>, GetBERTResult,
              (const gnoi::diag::GetBERTResultRequest &request));
  MOCK_METHOD(absl::StatusOr<absl::flat_hash_set<std::string>>, GetUpLinks,
              (absl::Span<const std::string> sut_ports), (override));
  MOCK_METHOD(absl::Status, CheckUp, (), (override));
  MOCK_METHOD(absl::Status, ValidatePortsUp,
              (absl::Span<const std::string> interfaces), (override));
  MOCK_METHOD(absl::Status, FlapLinks,
              (absl::string_view interface, absl::Duration down_duration),
              (override));
  MOCK_METHOD((absl::StatusOr<absl::flat_hash_map<std::string, int>>),
              GetInterfaceLaneSpeed,
              (absl::flat_hash_set<std::string> & interfaces), (override));
  MOCK_METHOD(absl::StatusOr<std::vector<std::string>>,
              FilterCollateralDownOnAdminDownInterfaces,
              (absl::Span<const std::string> interfaces), (override));
};

} // namespace thinkit

#endif // PINS_THINKIT_MOCK_CONTROL_DEVICE_H_

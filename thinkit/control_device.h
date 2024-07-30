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

#ifndef PINS_THINKIT_CONTROL_DEVICE_H_
#define PINS_THINKIT_CONTROL_DEVICE_H_

#include <functional>
#include <memory>
#include <string>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "diag/diag.grpc.pb.h"
#include "diag/diag.pb.h"
#include "thinkit/packet_generation_finalizer.h"

namespace thinkit {

enum class LinkState {
  kUnknown,
  kUp,
  kDown,
};

enum class RebootType {
  kUnknown,
  kWarm,
  kCold,
};

// Callback when a packet is received, first parameter which is control
// interface port it was received on and second parameter is the raw byte string
// of the packet.
using PacketCallback =
    std::function<void(absl::string_view, absl::string_view)>;

// A `ControlDevice` represents any device or devices that can at the very
// least send and receive packets over their interfaces. It may be able to get
// and set link state, as well as perform various other operations like link
// qualification or reboot.
class ControlDevice {
 public:
  virtual ~ControlDevice() {}

  // Starts collecting packets, calling `callback` whenever a packet is
  // received. This continues until the `PacketGenerationFinalizer` goes out of
  // scope.
  virtual absl::StatusOr<std::unique_ptr<thinkit::PacketGenerationFinalizer>>
  CollectPackets(PacketCallback callback) = 0;

  // Sends a `packet` raw byte string out of the control device’s
  // `interface`.
  virtual absl::Status SendPacket(absl::string_view interface,
                                  absl::string_view packet) = 0;

  // Check whether the ControlDevice implementation supports SendPacket - not
  // all control devices support it.
  virtual bool SupportsSendPacket() const = 0;

  // Sends a list of `packet` raw byte string out of the control
  // device’s `interface`.
  virtual absl::Status SendPackets(absl::string_view interface,
                                   absl::Span<const std::string> packets) = 0;

  // Sets the admin link state on the control device's 'interfaces'.
  virtual absl::Status SetAdminLinkState(
      absl::Span<const std::string> interfaces, LinkState state) = 0;

  // Reboots the control device.
  virtual absl::Status Reboot(RebootType reboot_type) = 0;

  // BERT functions.
  virtual absl::StatusOr<gnoi::diag::StartBERTResponse> StartBERT(
      const gnoi::diag::StartBERTRequest& request) = 0;

  virtual absl::StatusOr<gnoi::diag::StopBERTResponse> StopBERT(
      const gnoi::diag::StopBERTRequest& request) = 0;

  virtual absl::StatusOr<gnoi::diag::GetBERTResultResponse> GetBERTResult(
      const gnoi::diag::GetBERTResultRequest& request) = 0;

  // Gets which control device’s `interfaces` are admin and operationally up.
  virtual absl::StatusOr<absl::flat_hash_set<std::string>> GetUpLinks(
      absl::Span<const std::string> interfaces) = 0;

  // Checks if the control device is up. This implies that it is in a state that
  // it can perform its operations. This can be used to check when the control
  // device is ready after a reboot.
  virtual absl::Status CheckUp() = 0;
};

}  // namespace thinkit

#endif  // PINS_THINKIT_CONTROL_DEVICE_H_

// Copyright 2020 Google LLC
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
#include "p4rt_app/p4runtime/sdn_controller_manager.h"

#include <cstdint>
#include <optional>

#include "absl/log/log.h"
#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/types/optional.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"

namespace p4rt_app {
namespace {

std::string PrettyPrintDeviceId(const std::optional<uint64_t>& id) {
  return (id.has_value()) ? absl::StrCat("'", *id, "'") : "<unset>";
}

std::string PrettyPrintRoleName(const std::optional<std::string>& name) {
  return (name.has_value()) ? absl::StrCat("'", *name, "'") : "<default>";
}

std::string PrettyPrintElectionId(const std::optional<absl::uint128>& id) {
  if (id.has_value()) {
    p4::v1::Uint128 p4_id;
    p4_id.set_high(absl::Uint128High64(*id));
    p4_id.set_low(absl::Uint128Low64(*id));
    return absl::StrCat("{ ", p4_id.ShortDebugString(), " }");
  }
  return "<backup>";
}

grpc::Status VerifyElectionIdIsUnused(
    const std::optional<std::string>& role_name,
    const std::optional<absl::uint128>& election_id,
    absl::Span<const SdnConnection* const> active_connections,
    SdnConnection const* current_connection) {
  // If the election ID is not set then the controller is saying this should be
  // a backup connection, and we allow any number of backup connections.
  if (!election_id.has_value()) return grpc::Status::OK;

  // Otherwise, we verify the election ID is unique among all active connections
  // for a given role (excluding the root role).
  for (auto* connection : active_connections) {
    if (connection == current_connection) continue;
    if (connection->GetRoleName() == role_name &&
        connection->GetElectionId() == election_id) {
      return grpc::Status(grpc::StatusCode::INVALID_ARGUMENT,
                          "Election ID is already used by another connection "
                          "with the same role.");
    }
  }
  return grpc::Status::OK;
}

grpc::Status VerifyElectionIdIsActive(
    const std::optional<std::string>& role_name,
    const std::optional<absl::uint128>& election_id,
    absl::Span<const SdnConnection* const> active_connections) {
  for (const auto& connection : active_connections) {
    if (connection->GetRoleName() == role_name &&
        connection->GetElectionId() == election_id) {
      return grpc::Status::OK;
    }
  }
  return grpc::Status(grpc::StatusCode::PERMISSION_DENIED,
                      "Election ID is not active for the role.");
}

}  // namespace

void SdnConnection::SetElectionId(const std::optional<absl::uint128>& id) {
  election_id_ = id;
}

std::optional<absl::uint128> SdnConnection::GetElectionId() const {
  return election_id_;
}

void SdnConnection::SetRoleName(const std::optional<std::string>& name) {
  role_name_ = name;
}

std::optional<std::string> SdnConnection::GetRoleName() const {
  return role_name_;
}

void SdnConnection::SendStreamMessageResponse(
    const p4::v1::StreamMessageResponse& response) {
  VLOG(2) << "Sending response: " << response.ShortDebugString();
  if (!grpc_stream_->Write(response)) {
    LOG(ERROR) << "Could not send arbitration update response to gRPC conext '"
               << grpc_context_ << "': " << response.ShortDebugString();
  }
}

grpc::Status SdnControllerManager::HandleArbitrationUpdate(
    const p4::v1::MasterArbitrationUpdate& update, SdnConnection* controller) {
  absl::MutexLock l(&lock_);

  // If the Device ID has not been set then we don't allow any connections.
  if (!device_id_.has_value()) {
    return grpc::Status(
        grpc::StatusCode::FAILED_PRECONDITION,
        "Switch does not have a Device ID. Has a config been pushed?");
  }
  uint64_t device_id = *device_id_;

  // If the role name is not set then we assume the connection is a 'root'
  // connection.
  std::optional<std::string> role_name;
  if (update.has_role() && !update.role().name().empty()) {
    role_name = update.role().name();
  }

  const auto old_election_id_for_connection = controller->GetElectionId();
  std::optional<absl::uint128> new_election_id_for_connection;
  if (update.has_election_id()) {
    new_election_id_for_connection = absl::MakeUint128(
        update.election_id().high(), update.election_id().low());
  }

  const bool new_connection = !controller->IsInitialized();

  if (new_connection) {
    // First arbitration message sent by this controller.

    // Verify the request's device ID is being sent to the correct device.
    if (update.device_id() != device_id) {
      return grpc::Status(
          grpc::StatusCode::NOT_FOUND,
          absl::StrCat("Arbitration request has the wrong device ID '",
                       update.device_id(),
                       "'. Cannot establish connection to this device '",
                       device_id, "'."));
    }

    // Check if the election ID is being use by another connection.
    auto election_id_is_unused = VerifyElectionIdIsUnused(
        role_name, new_election_id_for_connection, connections_, controller);
    if (!election_id_is_unused.ok()) {
      return election_id_is_unused;
    }

    controller->SetRoleName(role_name);
    controller->SetElectionId(new_election_id_for_connection);
    controller->Initialize();
    connections_.push_back(controller);
    LOG(INFO) << "New SDN connection: " << update.ShortDebugString();
  } else {
    // Update arbitration message sent from the controller.

    // The device ID cannot change.
    if (update.device_id() != device_id) {
      return grpc::Status(
          grpc::StatusCode::FAILED_PRECONDITION,
          absl::StrCat("Arbitration request cannot change the device ID from '",
                       device_id, "' to '", update.device_id(), "'."));
    }

    // The role cannot change without closing the connection.
    if (role_name != controller->GetRoleName()) {
      return grpc::Status(
          grpc::StatusCode::FAILED_PRECONDITION,
          absl::StrCat("Arbitration request cannot change the role from ",
                       PrettyPrintRoleName(controller->GetRoleName()), " to ",
                       PrettyPrintRoleName(role_name), "."));
    }

    // Check if the election ID is being use by another connection.
    auto election_id_is_unused = VerifyElectionIdIsUnused(
        role_name, new_election_id_for_connection, connections_, controller);
    if (!election_id_is_unused.ok()) {
      return election_id_is_unused;
    }
    controller->SetElectionId(new_election_id_for_connection);

    LOG(INFO) << absl::StreamFormat(
        "Update SDN connection (%s, %s): %s",
        PrettyPrintRoleName(controller->GetRoleName()),
        PrettyPrintElectionId(controller->GetElectionId()),
        update.ShortDebugString());
  }

  // Check for any primary connection changes, and inform all active connections
  // as needed.
  auto& election_id_past_for_role = election_id_past_by_role_[role_name];
  const bool connection_was_primary =
      old_election_id_for_connection.has_value() &&
      old_election_id_for_connection == election_id_past_for_role;
  const bool connection_is_new_primary =
      new_election_id_for_connection.has_value() &&
      (!election_id_past_for_role.has_value() ||
       *new_election_id_for_connection >= *election_id_past_for_role);

  if (connection_is_new_primary) {
    election_id_past_for_role = new_election_id_for_connection;
    // The spec demands we send a notifcation even if the old & new primary
    // match.
    InformConnectionsAboutPrimaryChange(role_name);
    LOG(INFO) << (connection_was_primary ? "Old and new " : "New ")
              << "primary connection for role "
              << PrettyPrintRoleName(role_name) << " with election ID "
              << PrettyPrintElectionId(*new_election_id_for_connection) << ".";
    // If there was a previous primary, we need to ensure write requests by the
    // old primary and new primary are not interleaved, and the spec carefully
    // specifies how to do this.
    // Our implementation simply rules out all interleavings by using a common
    // lock, so no special handling is needed here.
  } else {
    if (connection_was_primary) {
      // This connection was previosuly the primary and downgrades to backup.
      InformConnectionsAboutPrimaryChange(role_name);
      LOG(INFO) << "Primary connection for role "
                << PrettyPrintRoleName(role_name)
                << " is downgrading to backup with election ID "
                << PrettyPrintElectionId(new_election_id_for_connection)
                << "; no longer have a primary.";
    } else {
      SendArbitrationResponse(controller);
      LOG(INFO) << "Backup connection for role "
                << PrettyPrintRoleName(role_name) << " with "
                << (new_connection ? "initial " : "changed ") << "election ID "
                << PrettyPrintElectionId(new_election_id_for_connection);
    }
  }
  return grpc::Status::OK;
}

void SdnControllerManager::Disconnect(SdnConnection* connection) {
  absl::MutexLock l(&lock_);

  // If the connection was never initialized then there is no work needed to
  // disconnect it.
  if (!connection->IsInitialized()) return;

  // Iterate through the list connections and remove this connection.
  for (auto iter = connections_.begin(); iter != connections_.end(); ++iter) {
    if (*iter == connection) {
      LOG(INFO) << "Dropping SDN connection for role "
                << PrettyPrintRoleName(connection->GetRoleName())
                << " with election ID "
                << PrettyPrintElectionId(connection->GetElectionId()) << ".";
      connections_.erase(iter);
      break;
    }
  }

  // If connection was the primary connection we need to inform all existing
  // connections.
  if (connection->GetElectionId().has_value() &&
      (connection->GetElectionId() ==
       election_id_past_by_role_[connection->GetRoleName()])) {
    InformConnectionsAboutPrimaryChange(connection->GetRoleName());
  }
}

absl::Status SdnControllerManager::SetDeviceId(uint64_t device_id) {
  absl::MutexLock l(&lock_);

  // Ignore no-ops on Device ID values.
  if (device_id_.has_value() && *device_id_ == device_id) {
    return absl::OkStatus();
  }

  // Cannot change the Device ID while we have any active connections.
  if (!connections_.empty()) {
    return gutil::FailedPreconditionErrorBuilder()
           << "Device ID cannot be changed while a controller is connected.";
  }

  // Zero is an assumed default for proto3 so we treat it as if the device ID is
  // unset.
  if (device_id == 0) {
    LOG(WARNING) << "Removing Device ID.";
    device_id_ = std::nullopt;
    return absl::OkStatus();
  }

  if (device_id_.has_value()) {
    LOG(WARNING) << "Changing device ID from " << *device_id_ << " to "
                 << device_id << ".";
  } else {
    LOG(INFO) << "Setting device ID to " << device_id << ".";
  }
  device_id_ = device_id;
  return absl::OkStatus();
}

std::optional<uint64_t> SdnControllerManager::GetDeviceId() const {
  absl::MutexLock l(&lock_);
  return device_id_;
}

grpc::Status SdnControllerManager::AllowMutableRequest(
    const std::optional<uint64_t>& device_id,
    const std::optional<std::string>& role_name,
    const std::optional<absl::uint128>& election_id) const {
  absl::MutexLock l(&lock_);

  // Both the switch and request must have a device ID, and they must match
  // before we allow the request to mutate state.
  if (!device_id.has_value()) {
    return grpc::Status(grpc::StatusCode::NOT_FOUND,
                        "Request does not have a device ID.");
  }
  if (device_id != device_id_) {
    return grpc::Status(grpc::StatusCode::NOT_FOUND,
                        absl::StrCat("Request's device ID '", *device_id,
                                     "' does not the match switch's ",
                                     PrettyPrintDeviceId(device_id_), "."));
  }

  // Furthermore, the request must be from the primary connection.
  if (!election_id.has_value()) {
    return grpc::Status(grpc::StatusCode::PERMISSION_DENIED,
                        "Request does not have an election ID.");
  }
  const auto& election_id_past_for_role =
      election_id_past_by_role_.find(role_name);
  if (election_id_past_for_role == election_id_past_by_role_.end()) {
    return grpc::Status(grpc::StatusCode::PERMISSION_DENIED,
                        "Only the primary connection can issue requests, but "
                        "no primary connection has been established.");
  }
  if (election_id != election_id_past_for_role->second) {
    return grpc::Status(grpc::StatusCode::PERMISSION_DENIED,
                        "Only the primary connection can issue requests.");
  }
  return VerifyElectionIdIsActive(role_name, election_id, connections_);
}

grpc::Status SdnControllerManager::AllowNonMutableRequest(
    const std::optional<uint64_t>& device_id) const {
  absl::MutexLock l(&lock_);

  // Both the switch and request must have a device ID, and they must match
  // before we allow a request to read any state.
  if (!device_id.has_value()) {
    return grpc::Status(grpc::StatusCode::NOT_FOUND,
                        "Request does not have a device ID.");
  }
  if (device_id != device_id_) {
    return grpc::Status(grpc::StatusCode::NOT_FOUND,
                        absl::StrCat("Request's device ID '", *device_id,
                                     "' does not the match switch's ",
                                     PrettyPrintDeviceId(device_id_), "."));
  }

  // However, it does not need to be the primary. In fact there doesn't even
  // need to be an active connection per the spec.
  return grpc::Status::OK;
}

grpc::Status SdnControllerManager::AllowRequest(
    const p4::v1::WriteRequest& request) const {
  std::optional<uint64_t> device_id;
  std::optional<std::string> role_name;
  std::optional<absl::uint128> election_id;

  if (request.device_id() != 0) {
    device_id = request.device_id();
  }
  if (!request.role().empty()) {
    role_name = request.role();
  }
  if (request.has_election_id()) {
    election_id = absl::MakeUint128(request.election_id().high(),
                                    request.election_id().low());
  }

  // Write requests can mutate switch state.
  return AllowMutableRequest(device_id, role_name, election_id);
}

grpc::Status SdnControllerManager::AllowRequest(
    const p4::v1::ReadRequest& request) const {
  std::optional<uint64_t> device_id;
  if (request.device_id() != 0) {
    device_id = request.device_id();
  }

  // Read requests will not mutate switch state.
  return AllowNonMutableRequest(device_id);
}

grpc::Status SdnControllerManager::AllowRequest(
    const p4::v1::SetForwardingPipelineConfigRequest& request) const {
  std::optional<uint64_t> device_id;
  std::optional<std::string> role_name;
  std::optional<absl::uint128> election_id;

  if (request.device_id() != 0) {
    device_id = request.device_id();
  }
  if (!request.role().empty()) {
    role_name = request.role();
  }
  if (request.has_election_id()) {
    election_id = absl::MakeUint128(request.election_id().high(),
                                    request.election_id().low());
  }

  // Setting the forwarding pipeline can mutate the switch state.
  return AllowMutableRequest(device_id, role_name, election_id);
}

grpc::Status SdnControllerManager::AllowRequest(
    const p4::v1::GetForwardingPipelineConfigRequest& request) const {
  std::optional<uint64_t> device_id;
  if (request.device_id() != 0) {
    device_id = request.device_id();
  }

  // Getting the forwarding pipeline will not mutate switch state.
  return AllowNonMutableRequest(device_id);
}

grpc::Status SdnControllerManager::AllowRequest(
    const p4::v1::CapabilitiesRequest& request) const {
  if (request.device_id() == 0) {
    return grpc::Status(grpc::StatusCode::UNIMPLEMENTED,
                        "CapabilitiesRequest does not have a device ID.");
  }

  std::optional<uint64_t> device_id = request.device_id();
  // Getting the capabilities will not mutate switch state.
  return AllowNonMutableRequest(device_id);
}

void SdnControllerManager::InformConnectionsAboutPrimaryChange(
    const std::optional<std::string>& role_name) {
  VLOG(1) << "Informing all connections about primary connection change.";
  for (const auto& connection : connections_) {
    if (connection->GetRoleName() == role_name) {
      SendArbitrationResponse(connection);
    }
  }
}

bool SdnControllerManager::PrimaryConnectionExists(
    const std::optional<std::string>& role_name) {
  std::optional<absl::uint128> election_id_past_for_role =
      election_id_past_by_role_[role_name];

  for (const auto& connection : connections_) {
    if (connection->GetRoleName() == role_name &&
        connection->GetElectionId() == election_id_past_for_role) {
      return election_id_past_for_role.has_value();
    }
  }
  return false;
}

void SdnControllerManager::SendArbitrationResponse(SdnConnection* connection) {
  p4::v1::StreamMessageResponse response;
  auto arbitration = response.mutable_arbitration();

  // Only set the device ID if it has been configed.
  if (device_id_.has_value()) {
    arbitration->set_device_id(*device_id_);
  }

  // Populate the role only if the connection has set one.
  if (connection->GetRoleName().has_value()) {
    *arbitration->mutable_role()->mutable_name() =
        connection->GetRoleName().value();
  }

  // Populate the election ID with the highest accepted value.
  std::optional<absl::uint128> election_id_past_for_role =
      election_id_past_by_role_[connection->GetRoleName()];
  if (election_id_past_for_role.has_value()) {
    arbitration->mutable_election_id()->set_high(
        absl::Uint128High64(election_id_past_for_role.value()));
    arbitration->mutable_election_id()->set_low(
        absl::Uint128Low64(election_id_past_for_role.value()));
  }

  // Update connection status for the arbitration response.
  auto status = arbitration->mutable_status();
  if (PrimaryConnectionExists(connection->GetRoleName())) {
    // has primary connection.
    if (election_id_past_for_role == connection->GetElectionId()) {
      // and this connection is it.
      status->set_code(grpc::StatusCode::OK);
      status->set_message("you are the primary connection.");
    } else {
      // but this connection is a backup.
      status->set_code(grpc::StatusCode::ALREADY_EXISTS);
      status->set_message(
          "you are a backup connection, and a primary connection exists.");
    }
  } else {
    // no primary connection exists.
    status->set_code(grpc::StatusCode::NOT_FOUND);
    status->set_message(
        "you are a backup connection, and NO primary connection exists.");
  }

  connection->SendStreamMessageResponse(response);
}

absl::Status SdnControllerManager::SendPacketInToPrimary(
    const p4::v1::StreamMessageResponse& response) {
  if (response.update_case() != p4::v1::StreamMessageResponse::kPacket) {
    LOG(WARNING) << "PacketIn stream message update has to be a packet: "
                 << response.ShortDebugString();
    return gutil::InvalidArgumentErrorBuilder()
           << "PacketIn message must use a packet.";
  }
  return SendStreamMessageToPrimary(response);
}

absl::Status SdnControllerManager::SendStreamMessageToPrimary(
    const p4::v1::StreamMessageResponse& response) {
  absl::MutexLock l(&lock_);

  bool found_at_least_one_primary = false;

  for (const auto& connection : connections_) {
    auto role_name = connection->GetRoleName();

    auto primary_id_by_role_name = gutil::FindOrDefault(
        election_id_past_by_role_, role_name, std::nullopt);
    if (primary_id_by_role_name.has_value() &&
        primary_id_by_role_name == connection->GetElectionId()) {
      if (role_receives_packet_in_.contains(role_name)) {
        found_at_least_one_primary = true;
        connection->SendStreamMessageResponse(response);
      }
    }
  }

  if (!found_at_least_one_primary) {
    LOG_EVERY_N_SEC(WARNING, 30)
        << "Cannot send stream message response because there is no "
        << "active primary connection: " << response.ShortDebugString();
    return gutil::FailedPreconditionErrorBuilder()
           << "No active role has a primary connection configured to receive "
              "PacketIn messages.";
  }
  return absl::OkStatus();
}

}  // namespace p4rt_app

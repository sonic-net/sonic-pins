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

// Auxiliary functions for mocking P4RuntimeSession behaviors.

#ifndef PINS_P4_INFRA_P4_RUNTIME_P4_RUNTIME_SESSION_MOCKING_H_
#define PINS_P4_INFRA_P4_RUNTIME_P4_RUNTIME_SESSION_MOCKING_H_

#include <vector>

#include "absl/strings/string_view.h"
#include "absl/types/optional.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4/v1/p4runtime_mock.grpc.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"

namespace p4_runtime {

// A fixed P4Runtime device ID used in requests returned by the
// `Construct*Request` functions in this file.
constexpr uint32_t kDeviceId = 100;

// An initialized `P4RuntimeSession` together with a `MockP4RuntimeStub` that
// the session is connected to. Useful for testing methods/free functions
// of/on `P4RuntimeSession`.
struct P4SessionWithMockStub {
  std::unique_ptr<P4RuntimeSession> p4rt_session;
  // Owned by the `p4rt_session`.
  p4::v1::MockP4RuntimeStub& mock_p4rt_stub;
};

// Creates a `P4RuntimeSession` based on a mocked `P4RuntimeStub`. Useful for
// testing methods/free functions of/on `P4RuntimeSession`.
absl::StatusOr<P4SessionWithMockStub> MakeP4SessionWithMockStub(
    const P4RuntimeSessionOptionalArgs& metadata);

p4::v1::Uint128 ConstructElectionId(
    const P4RuntimeSessionOptionalArgs& metadata);

p4::v1::MasterArbitrationUpdate ConstructMasterArbitrationUpdate(
    const P4RuntimeSessionOptionalArgs& metadata);

// Constructs a generic table entry.
p4::v1::TableEntry ConstructTableEntry();

// Sets up a write request to delete the given entities.
p4::v1::WriteRequest ConstructDeleteRequest(
    const P4RuntimeSessionOptionalArgs& metadata,
    const std::vector<p4::v1::Entity>& entities);

// Constructs a valid forwarding pipeline config request with the given p4info
// and metadata.
p4::v1::SetForwardingPipelineConfigRequest
ConstructForwardingPipelineConfigRequest(
    const P4RuntimeSessionOptionalArgs& metadata,
    const p4::config::v1::P4Info& p4info,
    p4::v1::SetForwardingPipelineConfigRequest::Action action,
    absl::optional<absl::string_view> p4_device_config = absl::nullopt);

// Configures the given `MockP4RuntimeStub` such that the given sequence of
// entities will be returned for the next P4RT Read request.
void SetNextReadResponse(p4::v1::MockP4RuntimeStub& mock_p4rt_stub,
                         std::vector<p4::v1::Entity> read_entities);

// Configures the given `MockP4RuntimeStub` such that the given sequence of
// table entries will be returned for the next P4RT Read request.
void SetNextReadResponse(p4::v1::MockP4RuntimeStub& mock_p4rt_stub,
                         std::vector<p4::v1::TableEntry> read_entries);

// Configures the given `MockP4RuntimeStub` such that the given sequence of
// entities will be returned for any P4RT Read request by default.
void SetDefaultReadResponse(p4::v1::MockP4RuntimeStub& mock_p4rt_stub,
                            std::vector<p4::v1::Entity> read_entities);

// Configures the given `MockP4RuntimeStub` such that the given sequence of
// table entries will be returned for any P4RT Read request by default.
void SetDefaultReadResponse(p4::v1::MockP4RuntimeStub& mock_p4rt_stub,
                            std::vector<p4::v1::TableEntry> read_entries);

// Mocks a P4RuntimeSession::Create call with a stub by constructing a
// ReaderWriter mock stream and mocking an arbitration handshake. This function
// does not perform any of these operations, it only sets up expectations.
//
// NOTE: Not suitable for tests that need to mock stream channel reads, since
// this function does not expose the stream channel mock.
void MockP4RuntimeSessionCreate(p4::v1::MockP4RuntimeStub& stub,
                                const P4RuntimeSessionOptionalArgs& metadata);

// Mocks a `CheckNoEntities` call using the stub in a previously
// mocked P4RuntimeSession.
// Ensures that there are no entities remaining.
void MockCheckNoEntities(p4::v1::MockP4RuntimeStub& stub,
                         std::optional<p4::config::v1::P4Info> p4info);

// Mocks a ClearEntities call using the stub and p4info in a previously
// mocked P4RuntimeSession.
// Pulls the p4info from the switch, then reads a table entry and a multicast
// entity, deletes them, and reads again ensuring that there are no entities
// remaining.
void MockClearEntities(p4::v1::MockP4RuntimeStub& stub,
                       const p4::config::v1::P4Info& p4info,
                       const P4RuntimeSessionOptionalArgs& metadata);

// Mocks a `CheckNoEntries` call using the stub in a previously
// mocked P4RuntimeSession.
// Ensures that there are no table entries remaining.
ABSL_DEPRECATED(
    "Use MockCheckNoEntities instead due to transition to using entities "
void MockCheckNoEntries(p4::v1::MockP4RuntimeStub& stub,
                        std::optional<p4::config::v1::P4Info> p4info);

// Mocks a ClearTableEntries call using the stub and p4info in a previously
// mocked P4RuntimeSession.
// Pulls the p4info from the switch, then reads a table entry, deletes it, and
// reads again ensuring that there are no table entries remaining.
ABSL_DEPRECATED(
    "Use MockClearEntities instead due to transition to using entities "
void MockClearTableEntries(p4::v1::MockP4RuntimeStub& stub,
                           const p4::config::v1::P4Info& p4info,
                           const P4RuntimeSessionOptionalArgs& metadata);

}  // namespace p4_runtime

#endif  // PINS_P4_INFRA_P4_RUNTIME_P4_RUNTIME_SESSION_MOCKING_H_

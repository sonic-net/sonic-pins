// Copyright 2021 Google LLC
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
#include <cstdint>
#include <memory>
#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_join.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/app_db_entry_builder.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::Contains;
using ::testing::ElementsAre;
using ::testing::ExplainMatchResult;
using ::testing::HasSubstr;
using ::testing::IsEmpty;
using ::testing::Not;
using ::testing::UnorderedElementsAreArray;

// Expects a DB to contain the provided port map.
MATCHER_P2(
    ContainsPortMap, port_name, port_id,
    absl::Substitute("Contains mapping of port_name '$0' to port id '$1'",
                     port_name, port_id)) {
  return ExplainMatchResult(
      IsOkAndHolds(ElementsAre(std::make_pair("id", port_id))),
      arg.ReadTableEntry(port_name), result_listener);
}

// Expects a DB to contain the provided AppDB flow entry.
MATCHER_P(
    ContainsAppDbEntry, app_db_entry,
    absl::Substitute("Contains an APP DB entry with key '$0' and entries [$1]",
                     app_db_entry.GetKey(),
                     absl::StrJoin(app_db_entry.GetValueList(), ", ",
                                   absl::PairFormatter("=")))) {
  return ExplainMatchResult(
      IsOkAndHolds(UnorderedElementsAreArray(app_db_entry.GetValueMap())),
      arg.ReadTableEntry(app_db_entry.GetKey()), result_listener);
}

absl::StatusOr<p4::v1::WriteRequest> WriteRequestWithPort(
    const pdpi::IrP4Info& ir_p4_info, absl::string_view port) {
  return test_lib::PdWriteRequestToPi(
      absl::Substitute(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                router_interface_table_entry {
                  match { router_interface_id: "16" }
                  action {
                    set_port_and_src_mac {
                      port: "$0"
                      src_mac: "00:02:03:04:05:06"
                    }
                  }
                }
              }
            }
          )pb",
          port),
      ir_p4_info);
}

test_lib::AppDbEntryBuilder AppDbEntryWithPort(absl::string_view port) {
  test_lib::AppDbEntryBuilder builder;
  return builder.SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
      .AddMatchField("router_interface_id", "16")
      .SetAction("set_port_and_src_mac")
      .AddActionParam("port", std::string(port))
      .AddActionParam("src_mac", "00:02:03:04:05:06");
}

class PortNameAndIdTest : public test_lib::P4RuntimeComponentTestFixture {
 public:
  PortNameAndIdTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock,
            P4RuntimeImplOptions{.translate_port_ids = true}) {}
};

TEST_F(PortNameAndIdTest, TranslatesPortIdToName) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK_AND_ASSIGN(auto request, WriteRequestWithPort(ir_p4_info_, "1"));
  test_lib::AppDbEntryBuilder app_db_entry = AppDbEntryWithPort("Ethernet0");

  ASSERT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  EXPECT_THAT(p4rt_service_.GetP4rtAppDbTable(),
              ContainsAppDbEntry(AppDbEntryWithPort("Ethernet0")));
}

TEST_F(PortNameAndIdTest, AddTranslationUpdatesAppDb) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  EXPECT_THAT(p4rt_service_.GetPortAppDbTable(),
              ContainsPortMap("Ethernet0", "1"));
  EXPECT_THAT(p4rt_service_.GetPortAppStateDbTable(),
              ContainsPortMap("Ethernet0", "1"));
}

TEST_F(PortNameAndIdTest, PortIdTranslationFailsForUnknownPortId) {
  ASSERT_OK_AND_ASSIGN(auto request, WriteRequestWithPort(ir_p4_info_, "2"));
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("#1: INVALID_ARGUMENT")));

  // The port id is used in the action param, so it doesn't affect the key.
  EXPECT_THAT(p4rt_service_.GetP4rtAppDbTable().GetAllKeys(),
              Not(Contains(AppDbEntryWithPort("2").GetKey())));
}

TEST_F(PortNameAndIdTest, PortIdTranslationCanBeRemoved) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK(p4rt_service_.GetP4rtServer().RemovePortTranslation("Ethernet0"));

  ASSERT_OK_AND_ASSIGN(auto request, WriteRequestWithPort(ir_p4_info_, "1"));
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("#1: INVALID_ARGUMENT")));

  EXPECT_THAT(p4rt_service_.GetPortAppDbTable().GetAllKeys(), IsEmpty());
  EXPECT_THAT(p4rt_service_.GetPortAppStateDbTable().GetAllKeys(), IsEmpty());
}

TEST_F(PortNameAndIdTest, ResendingDuplicatePortTranslationsAreAllowed) {
  EXPECT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "0"));
  EXPECT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "0"));

  ASSERT_OK_AND_ASSIGN(auto request, WriteRequestWithPort(ir_p4_info_, "0"));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  EXPECT_THAT(p4rt_service_.GetP4rtAppDbTable(),
              ContainsAppDbEntry(AppDbEntryWithPort("Ethernet0")));

  EXPECT_THAT(p4rt_service_.GetPortAppDbTable(),
              ContainsPortMap("Ethernet0", "0"));
  EXPECT_THAT(p4rt_service_.GetPortAppStateDbTable(),
              ContainsPortMap("Ethernet0", "0"));
}

TEST_F(PortNameAndIdTest, PortNamesCanBeRemappedToUnusedPortIds) {
  EXPECT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "0"));
  EXPECT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));

  ASSERT_OK_AND_ASSIGN(auto request, WriteRequestWithPort(ir_p4_info_, "1"));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  EXPECT_THAT(p4rt_service_.GetP4rtAppDbTable(),
              ContainsAppDbEntry(AppDbEntryWithPort("Ethernet0")));
  EXPECT_THAT(p4rt_service_.GetPortAppDbTable(),
              ContainsPortMap("Ethernet0", "1"));
  EXPECT_THAT(p4rt_service_.GetPortAppStateDbTable(),
              ContainsPortMap("Ethernet0", "1"));
}

TEST_F(PortNameAndIdTest, RemappingPortNamesRemovesOldTranslations) {
  EXPECT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "0"));
  EXPECT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));

  ASSERT_OK_AND_ASSIGN(auto request, WriteRequestWithPort(ir_p4_info_, "0"));
  EXPECT_FALSE(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request)
          .ok());
}

TEST_F(PortNameAndIdTest, ReusingPortIdFailsWithAlreadyExists) {
  EXPECT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "0"));
  EXPECT_THAT(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1", "0"),
      StatusIs(absl::StatusCode::kAlreadyExists));
}

TEST_F(PortNameAndIdTest, ReusingPortIdFailureHasNoSideEffects) {
  EXPECT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "0"));
  ASSERT_THAT(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1", "0"),
      StatusIs(absl::StatusCode::kAlreadyExists));

  ASSERT_OK_AND_ASSIGN(auto request, WriteRequestWithPort(ir_p4_info_, "0"));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  EXPECT_THAT(p4rt_service_.GetP4rtAppDbTable(),
              ContainsAppDbEntry(AppDbEntryWithPort("Ethernet0")));
  EXPECT_THAT(p4rt_service_.GetPortAppDbTable(),
              ContainsPortMap("Ethernet0", "0"));
  EXPECT_THAT(p4rt_service_.GetPortAppStateDbTable(),
              ContainsPortMap("Ethernet0", "0"));
}

TEST_F(PortNameAndIdTest, ChangingPortIdWithRemovalUpdatesTranslations) {
  EXPECT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "10"));
  EXPECT_OK(p4rt_service_.GetP4rtServer().RemovePortTranslation("Ethernet0"));
  EXPECT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "11"));

  ASSERT_OK_AND_ASSIGN(auto request, WriteRequestWithPort(ir_p4_info_, "11"));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  EXPECT_THAT(p4rt_service_.GetP4rtAppDbTable(),
              ContainsAppDbEntry(AppDbEntryWithPort("Ethernet0")));
  EXPECT_THAT(p4rt_service_.GetPortAppDbTable(),
              ContainsPortMap("Ethernet0", "11"));
  EXPECT_THAT(p4rt_service_.GetPortAppStateDbTable(),
              ContainsPortMap("Ethernet0", "11"));
}

TEST_F(PortNameAndIdTest, CannotAddPortTranslationWithEmptyValues) {
  EXPECT_THAT(p4rt_service_.GetP4rtServer().AddPortTranslation("", "1"),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", ""),
              StatusIs(absl::StatusCode::kInvalidArgument));

  EXPECT_THAT(p4rt_service_.GetPortAppDbTable().GetAllKeys(), IsEmpty());
  EXPECT_THAT(p4rt_service_.GetPortAppStateDbTable().GetAllKeys(), IsEmpty());
}

TEST_F(PortNameAndIdTest, RemovingNonExistantPortTranslationPasses) {
  EXPECT_OK(p4rt_service_.GetP4rtServer().RemovePortTranslation("Ethernet0"));
}

TEST_F(PortNameAndIdTest, CannotRemovePortTranslationWithEmptyValues) {
  EXPECT_THAT(p4rt_service_.GetP4rtServer().RemovePortTranslation(""),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(PortNameAndIdTest, NameTranslationRoundTrip) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK_AND_ASSIGN(auto request, WriteRequestWithPort(ir_p4_info_, "1"));

  ASSERT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  EXPECT_THAT(pdpi::ReadPiTableEntries(p4rt_session_.get()),
              IsOkAndHolds(ElementsAre(
                  EqualsProto(request.updates(0).entity().table_entry()))));
}

class PortNameAndNameTest : public test_lib::P4RuntimeComponentTestFixture {
 public:
  PortNameAndNameTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock,
            P4RuntimeImplOptions{.translate_port_ids = false}) {}
};

TEST_F(PortNameAndNameTest, PassesPortNameToAppDb) {
  ASSERT_OK_AND_ASSIGN(auto request,
                       WriteRequestWithPort(ir_p4_info_, "Ethernet0"));
  ASSERT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  EXPECT_THAT(p4rt_service_.GetP4rtAppDbTable(),
              ContainsAppDbEntry(AppDbEntryWithPort("Ethernet0")));
}

TEST_F(PortNameAndNameTest, IgnoresMapping) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK_AND_ASSIGN(auto request,
                       WriteRequestWithPort(ir_p4_info_, "Ethernet0"));

  ASSERT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  EXPECT_THAT(p4rt_service_.GetP4rtAppDbTable(),
              ContainsAppDbEntry(AppDbEntryWithPort("Ethernet0")));
}

TEST_F(PortNameAndNameTest, NameTranslationRoundTrip) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK_AND_ASSIGN(auto request,
                       WriteRequestWithPort(ir_p4_info_, "Ethernet0"));
  ASSERT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  EXPECT_THAT(pdpi::ReadPiTableEntries(p4rt_session_.get()),
              IsOkAndHolds(ElementsAre(
                  EqualsProto(request.updates(0).entity().table_entry()))));
}

}  // namespace
}  // namespace p4rt_app

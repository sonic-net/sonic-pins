// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/forwarding/smoke_test.h"

#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "google/protobuf/util/message_differencer.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/test_data.h"

namespace pins_test {
namespace {

TEST_P(SmokeTestFixture, SessionsAreNonNull) {
  ASSERT_NE(&GetSutP4RuntimeSession(), nullptr);
  ASSERT_NE(&GetControlP4RuntimeSession(), nullptr);
}

TEST_P(SmokeTestFixture, AclTableAddDeleteOkButModifyFails) {
  const sai::WriteRequest pd_insert = gutil::ParseProtoOrDie<sai::WriteRequest>(
      R"pb(
        updates {
          type: INSERT
          table_entry {
            acl_ingress_table_entry {
              match { is_ip { value: "0x1" } }
              priority: 10
              action { acl_copy { qos_queue: "0x1" } }
            }
          }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest pi_insert,
                       pdpi::PdWriteRequestToPi(
		       sai::GetIrP4Info(sai::Instantiation::kMiddleblock), pd_insert));
  
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(&GetSutP4RuntimeSession(),
                                                   pi_insert));

  const sai::WriteRequest pd_modify = gutil::ParseProtoOrDie<sai::WriteRequest>(
      R"pb(
        updates {
          type: MODIFY
          table_entry {
            acl_ingress_table_entry {
              match { is_ip { value: "0x1" } }
              priority: 10
              action { acl_forward {} }
            }
          }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest pi_modify,
                       pdpi::PdWriteRequestToPi(
		       sai::GetIrP4Info(sai::Instantiation::kMiddleblock), pd_modify));
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(&GetSutP4RuntimeSession(),
                                                   pi_modify));
  
  // This used to fail with a read error.
  ASSERT_OK(pdpi::ClearTableEntries(&GetSutP4RuntimeSession()));
}

TEST_P(SmokeTestFixture, InsertTableEntry) {
  const sai::TableEntry pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
      R"pb(
        router_interface_table_entry {
          match { router_interface_id: "router-interface-1" }
          action {
            set_port_and_src_mac { port: "1" src_mac: "02:2a:10:00:00:03" }
          }
        }
      )pb");

  ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
		       sai::GetIrP4Info(sai::Instantiation::kMiddleblock), pd_entry));
  ASSERT_OK(pdpi::InstallPiTableEntry(&GetSutP4RuntimeSession(), pi_entry));
}

TEST_P(SmokeTestFixture, InsertTableEntryWithRandomCharacterId) {
  sai::TableEntry pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
      R"pb(
        router_interface_table_entry {
          match { router_interface_id: "\x01\x33\x00\xff,\":'}(*{+-" }
          action {
            set_port_and_src_mac { port: "1" src_mac: "02:2a:10:00:00:03" }
          }
        }
      )pb");

  ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
		       sai::GetIrP4Info(sai::Instantiation::kMiddleblock), pd_entry));
  ASSERT_OK(pdpi::InstallPiTableEntry(&GetSutP4RuntimeSession(), pi_entry));
  ASSERT_OK_AND_ASSIGN(auto entries,
                       pdpi::ReadPiTableEntries(&GetSutP4RuntimeSession()));
  ASSERT_EQ(entries.size(), 1);
  ASSERT_THAT(entries[0], gutil::EqualsProto(pi_entry));
}

TEST_P(SmokeTestFixture, InsertAndReadTableEntries) {
  pdpi::P4RuntimeSession& session = GetSutP4RuntimeSession();
  const pdpi::IrP4Info& ir_p4info = sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  std::vector<sai::TableEntry> write_pd_entries =
      sai_pd::CreateUpTo255GenericTableEntries(3);

  thinkit::TestEnvironment& test_environment = GetMirrorTestbed().Environment();
  std::vector<p4::v1::TableEntry> write_pi_entries;
  p4::v1::ReadResponse expected_read_response;
  write_pi_entries.reserve(write_pd_entries.size());
  for (const auto& pd_entry : write_pd_entries) {
    ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry pi_entry,
                         pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry));

    ASSERT_OK(test_environment.AppendToTestArtifact(
        "pi_entries_written.pb.txt",
        absl::StrCat(pi_entry.DebugString(), "\n")));
    *expected_read_response.add_entities()->mutable_table_entry() = pi_entry;
    write_pi_entries.push_back(std::move(pi_entry));
  }

  ASSERT_OK(pdpi::InstallPiTableEntries(&session, ir_p4info, write_pi_entries));

  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(&session, read_request));

  for (const auto& entity : read_response.entities()) {
    ASSERT_OK(test_environment.AppendToTestArtifact(
        "pi_entries_read_back.pb.txt",
        absl::StrCat(entity.table_entry().DebugString(), "\n")));
  }

  // Compare the result in proto format since the fields being compared are
  // nested and out of order. Also ignore any dynamic fields (e.g. counters).
  google::protobuf::util::MessageDifferencer diff;
  diff.set_repeated_field_comparison(
      google::protobuf::util::MessageDifferencer::RepeatedFieldComparison::
           AS_SET);
  diff.IgnoreField(
      p4::v1::TableEntry::descriptor()->FindFieldByName("counter_data"));
  EXPECT_TRUE(diff.Compare(read_response, expected_read_response))
      << "Expected: " << expected_read_response.DebugString()
      << "\nActual: " << read_response.DebugString();
}

// Ensures that both CreateWithP4InfoAndClearTables and ClearTableEntries
// properly clear the table entries of a table.
TEST_P(SmokeTestFixture, EnsureClearTables) {
  // Sets up initial session.
  ASSERT_OK_AND_ASSIGN(auto session,
                       pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(
                           GetMirrorTestbed().Sut(),  p4_info()));
  // The table should be clear after setup.
  ASSERT_OK(pdpi::CheckNoTableEntries(session.get()));
  // Sets up an example table entry.
  const sai::TableEntry pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
      R"pb(
        router_interface_table_entry {
          match { router_interface_id: "router-interface-1" }
          action {
            set_port_and_src_mac { port: "1" src_mac: "02:2a:10:00:00:03" }
          }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
		       sai::GetIrP4Info(sai::Instantiation::kMiddleblock), pd_entry));
  ASSERT_OK(
      pdpi::InstallPiTableEntries(session.get(), 
	      sai::GetIrP4Info(sai::Instantiation::kMiddleblock), {pi_entry}));
  ASSERT_OK(pdpi::ClearTableEntries(session.get()));
  // The table should be clear after clearing.
  ASSERT_OK(pdpi::CheckNoTableEntries(session.get()));
  
  ASSERT_OK(
      pdpi::InstallPiTableEntries(session.get(), 
	      sai::GetIrP4Info(sai::Instantiation::kMiddleblock), {pi_entry}));
  
  ASSERT_OK_AND_ASSIGN(auto session2,
                       pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(
                           GetMirrorTestbed().Sut(), p4_info()));
  
  // The table should be clear for both sessions after setting up a new session.
  ASSERT_OK(pdpi::CheckNoTableEntries(session.get()));
  ASSERT_OK(pdpi::CheckNoTableEntries(session2.get()));
}

}  // namespace
}  // namespace pins

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
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/test_data.h"

namespace pins {
namespace {

// TODO: modify failing because of policer attributes.
TEST_P(SmokeTestFixture, DISABLED_ModifyWorks) {
  const sai::WriteRequest pd_insert = gutil::ParseProtoOrDie<sai::WriteRequest>(
      R"pb(
        updates {
          type: INSERT
          table_entry {
            acl_ingress_table_entry {
              match { is_ip { value: "0x1" } }
              priority: 10
              action { copy { qos_queue: "0x1" } }
            }
          }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest pi_insert,
                       pdpi::PdWriteRequestToPi(IrP4Info(), pd_insert));
  ASSERT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(SutP4RuntimeSession(), pi_insert));

  const sai::WriteRequest pd_modify = gutil::ParseProtoOrDie<sai::WriteRequest>(
      R"pb(
        updates {
          type: MODIFY
          table_entry {
            acl_ingress_table_entry {
              match { is_ip { value: "0x1" } }
              priority: 10
              action { forward {} }
            }
          }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest pi_modify,
                       pdpi::PdWriteRequestToPi(IrP4Info(), pd_modify));
  ASSERT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(SutP4RuntimeSession(), pi_modify));
  // This used to fail with a read error, see b/185508142.
  ASSERT_OK(pdpi::ClearTableEntries(SutP4RuntimeSession()));
}

// TODO: Enable once the bug is fixed.
TEST_P(SmokeTestFixture, DISABLED_Bug181149419) {
  GetMirrorTestbed().Environment().SetTestCaseID(
      "e6ba12b7-18e0-4681-9562-87e2fc01d429");
  // Adding 8 mirror sessions should succeed.
  for (int i = 0; i < 8; i++) {
    sai::TableEntry pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
        R"pb(
          mirror_session_table_entry {
            match { mirror_session_id: "session" }
            action {
              mirror_as_ipv4_erspan {
                port: "1"
                src_ip: "10.206.196.0"
                dst_ip: "172.20.0.202"
                src_mac: "00:02:03:04:05:06"
                dst_mac: "00:1a:11:17:5f:80"
                ttl: "0x40"
                tos: "0x00"
              }
            }
          }
        )pb");
    pd_entry.mutable_mirror_session_table_entry()
        ->mutable_match()
        ->set_mirror_session_id(absl::StrCat("session-", i));

    ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry pi_entry,
                         pdpi::PartialPdTableEntryToPiTableEntry(IrP4Info(), pd_entry));
    EXPECT_OK(pdpi::InstallPiTableEntry(SutP4RuntimeSession(), pi_entry));
  }
  // Adding one entry above the limit will fail.
  {
    sai::TableEntry pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
        R"pb(
          mirror_session_table_entry {
            match { mirror_session_id: "session-9" }
            action {
              mirror_as_ipv4_erspan {
                port: "1"
                src_ip: "10.206.196.0"
                dst_ip: "172.20.0.202"
                src_mac: "00:02:03:04:05:06"
                dst_mac: "00:1a:11:17:5f:80"
                ttl: "0x40"
                tos: "0x00"
              }
            }
          }
        )pb");

    ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry pi_entry,
                         pdpi::PartialPdTableEntryToPiTableEntry(IrP4Info(), pd_entry));
    EXPECT_FALSE(
        pdpi::InstallPiTableEntry(SutP4RuntimeSession(), pi_entry).ok());
  }
  // Adding ACL entries that use the 8 mirrors should all succeed.
  for (int i = 0; i < 8; i++) {
    sai::TableEntry pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
        R"pb(
          acl_ingress_table_entry {
            match {
              is_ipv4 { value: "0x1" }
              src_ip { value: "10.0.0.0" mask: "255.255.255.255" }
              dscp { value: "0x1c" mask: "0x3c" }
            }
            action { mirror { mirror_session_id: "session-1" } }
            priority: 2100
          }
        )pb");
    pd_entry.mutable_acl_ingress_table_entry()
        ->mutable_action()
        ->mutable_acl_mirror()
        ->set_mirror_session_id(absl::StrCat("session-", i));
    pd_entry.mutable_acl_ingress_table_entry()
        ->mutable_match()
        ->mutable_src_ip()
        ->set_value(absl::StrCat("10.0.0.", i));

    ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry pi_entry,
                         pdpi::PartialPdTableEntryToPiTableEntry(IrP4Info(), pd_entry));
    ASSERT_OK(pdpi::InstallPiTableEntry(SutP4RuntimeSession(), pi_entry));
  }
}

TEST_P(SmokeTestFixture, InsertTableEntry) {
  GetMirrorTestbed().Environment().SetTestCaseID(
      "da103fbb-8fd4-4385-b997-34e12a41004b");
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
                       pdpi::PartialPdTableEntryToPiTableEntry(IrP4Info(), pd_entry));
  ASSERT_OK(pdpi::InstallPiTableEntry(SutP4RuntimeSession(), pi_entry));
}

TEST_P(SmokeTestFixture, InsertTableEntryWithRandomCharacterId) {
  GetMirrorTestbed().Environment().SetTestCaseID(
      "bd22f5fe-4103-4729-91d0-cb2bc8258940");
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
                       pdpi::PartialPdTableEntryToPiTableEntry(IrP4Info(), pd_entry));
  ASSERT_OK(pdpi::InstallPiTableEntry(SutP4RuntimeSession(), pi_entry));
  ASSERT_OK_AND_ASSIGN(auto entries,
                       pdpi::ReadPiTableEntries(SutP4RuntimeSession()));
  ASSERT_EQ(entries.size(), 1);
  ASSERT_THAT(entries[0], gutil::EqualsProto(pi_entry));
}

TEST_P(SmokeTestFixture, InsertAndReadTableEntries) {
  GetMirrorTestbed().Environment().SetTestCaseID(
      "8bdacde4-b261-4242-b65d-462c828a427d");
  pdpi::P4RuntimeSession* session = SutP4RuntimeSession();
  const pdpi::IrP4Info& ir_p4info = IrP4Info();
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

  ASSERT_OK(pdpi::InstallPiTableEntries(session, ir_p4info, write_pi_entries));

  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(session, read_request));

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

}  // namespace
}  // namespace pins

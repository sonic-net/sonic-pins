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

#include "p4_infra/p4_pdpi/p4_runtime_session_extras.h"

#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "google/rpc/code.pb.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_mocking.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_infra/p4_pdpi/testing/test_p4info.h"

namespace pdpi {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOk;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::p4::config::v1::P4Info;
using ::p4::v1::GetForwardingPipelineConfigResponse;
using ::p4::v1::WriteRequest;
using ::testing::DoAll;
using ::testing::ElementsAre;
using ::testing::Not;
using ::testing::Return;
using ::testing::SaveArg;
using ::testing::SetArgPointee;
using ::testing::Unused;

TEST(InstallPdTableEntries,
     PullsP4InfoFromSwitchAndWritesPdpiTranslatedEntries) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  // The PD entries we will write to the switch...
  static constexpr absl::string_view kPdTableEntriesString = R"pb(
    entries {
      ternary_table_entry {
        match { normal { value: "0x0ff" mask: "0x0ff" } }
        action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
        priority: 1
      }
    }
  )pb";
  ASSERT_OK_AND_ASSIGN(
      const auto kPdTableEntries,
      gutil::ParseTextProto<pdpi::TableEntries>(kPdTableEntriesString));

  // ...and the translated PI entries that we expect will actually be sent to
  // the switch.
  ASSERT_OK_AND_ASSIGN(
      const std::vector<p4::v1::TableEntry> kPiTableEntries,
      PartialPdTableEntriesToPiTableEntries(ir_p4info, kPdTableEntries));
  p4::v1::Update expected_update;
  expected_update.set_type(p4::v1::Update::INSERT);
  *expected_update.mutable_entity()->mutable_table_entry() =
      kPiTableEntries.at(0);

  // Test `InstallPdTableEntries` overload taking parsed PD table entries.
  {
    ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                         MakeP4SessionWithMockStub(metadata));

    // Expect function to pull P4Info from switch.
    EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
        .WillOnce(
            [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
              *response->mutable_config()->mutable_p4info() = p4info;
              return grpc::Status::OK;
            });

    // Expect function to issue `Write` request with PD-to-PI-translated entry.
    EXPECT_CALL(mock_p4rt_stub, Write)
        .WillOnce([&](auto, const WriteRequest& request, auto) {
          EXPECT_THAT(request.updates(),
                      ElementsAre(EqualsProto(expected_update)));
          return grpc::Status::OK;
        });
    ASSERT_OK(InstallPdTableEntries(*p4rt_session, kPdTableEntries));
  }

  // Test `InstallPdTableEntries` overload taking PD table entries in text
  // format.
  {
    ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                         MakeP4SessionWithMockStub(metadata));

    // Expect function to pull P4Info from switch.
    EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
        .WillOnce(
            [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
              *response->mutable_config()->mutable_p4info() = p4info;
              return grpc::Status::OK;
            });

    // Expect function to issue `Write` request with PD-to-PI-translated entry.
    EXPECT_CALL(mock_p4rt_stub, Write)
        .WillOnce([&](auto, const WriteRequest& request, auto) {
          EXPECT_THAT(request.updates(),
                      ElementsAre(EqualsProto(expected_update)));
          return grpc::Status::OK;
        });
    ASSERT_OK(InstallPdTableEntries<pdpi::TableEntries>(*p4rt_session,
                                                        kPdTableEntriesString));
  }
}

TEST(InstallPdTableEntry, PullsP4InfoFromSwitchAndWritesPdpiTranslatedEntry) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  // The PD entry we will write to the switch...
  static constexpr absl::string_view kPdTableEntryString = R"pb(
    ternary_table_entry {
      match { normal { value: "0x0ff" mask: "0x0ff" } }
      action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
      priority: 1
    }
  )pb";
  ASSERT_OK_AND_ASSIGN(
      const auto kPdTableEntry,
      gutil::ParseTextProto<pdpi::TableEntry>(kPdTableEntryString));

  // ...and the translated PI entry that we expect will actually be sent to
  // the switch.
  ASSERT_OK_AND_ASSIGN(
      const p4::v1::TableEntry kPiTableEntry,
      PartialPdTableEntryToPiTableEntry(ir_p4info, kPdTableEntry));
  p4::v1::Update expected_update;
  expected_update.set_type(p4::v1::Update::INSERT);
  *expected_update.mutable_entity()->mutable_table_entry() = kPiTableEntry;

  // Test `InstallPdTableEntry` overload taking parsed PD table entry.
  {
    ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                         MakeP4SessionWithMockStub(metadata));

    // Expect function to pull P4Info from switch.
    EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
        .WillOnce(
            [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
              *response->mutable_config()->mutable_p4info() = p4info;
              return grpc::Status::OK;
            });

    // Expect function to issue `Write` request with PD-to-PI-translated entry.
    EXPECT_CALL(mock_p4rt_stub, Write)
        .WillOnce([&](auto, const WriteRequest& request, auto) {
          EXPECT_THAT(request.updates(),
                      ElementsAre(EqualsProto(expected_update)));
          return grpc::Status::OK;
        });
    ASSERT_OK(InstallPdTableEntry(*p4rt_session, kPdTableEntry));
  }

  // Test `InstallPdTableEntry` overload taking PD table entry in text
  // format.
  {
    ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                         MakeP4SessionWithMockStub(metadata));

    // Expect function to pull P4Info from switch.
    EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
        .WillOnce(
            [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
              *response->mutable_config()->mutable_p4info() = p4info;
              return grpc::Status::OK;
            });

    // Expect function to issue `Write` request with PD-to-PI-translated entry.
    EXPECT_CALL(mock_p4rt_stub, Write)
        .WillOnce([&](auto, const WriteRequest& request, auto) {
          EXPECT_THAT(request.updates(),
                      ElementsAre(EqualsProto(expected_update)));
          return grpc::Status::OK;
        });
    ASSERT_OK(InstallPdTableEntry<pdpi::TableEntry>(*p4rt_session,
                                                    kPdTableEntryString));
  }
}

TEST(InstallIrTableEntries,
     PullsP4InfoFromSwitchAndWritesPdpiTranslatedEntries) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });

  // PD version of our test entry for readability.
  ASSERT_OK_AND_ASSIGN(
      const auto kPdTableEntries,
      gutil::ParseTextProto<pdpi::TableEntries>(
          R"pb(
            entries {
              ternary_table_entry {
                match { normal { value: "0x0ff" mask: "0x0ff" } }
                action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
                priority: 1
              }
            }
          )pb"));

  // The IR entry that we will install on the switch...
  ASSERT_OK_AND_ASSIGN(
      const IrTableEntries kIrTableEntries,
      PartialPdTableEntriesToIrTableEntries(ir_p4info, kPdTableEntries));

  // ...and the translated PI entry that we expect will actually be sent to
  // the switch.
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::TableEntry> kPiTableEntries,
                       IrTableEntriesToPi(ir_p4info, kIrTableEntries));

  p4::v1::Update expected_update;
  expected_update.set_type(p4::v1::Update::INSERT);
  *expected_update.mutable_entity()->mutable_table_entry() =
      kPiTableEntries.at(0);

  // Expect function to issue `Write` request with IR-to-PI-translated entry.
  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(request.updates(),
                    ElementsAre(EqualsProto(expected_update)));
        return grpc::Status::OK;
      });
  ASSERT_OK(InstallIrTableEntries(*p4rt_session, kIrTableEntries));
}

TEST(InstallIrEntities, PullsP4InfoFromSwitchAndWritesPdpiTranslatedEntries) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });

  // PD version of our test entry for readability.
  ASSERT_OK_AND_ASSIGN(
      const auto kPdTableEntries,
      gutil::ParseTextProto<pdpi::TableEntries>(
          R"pb(
            entries {
              ternary_table_entry {
                match { normal { value: "0x0ff" mask: "0x0ff" } }
                action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
                priority: 1
              }
            }
          )pb"));

  // The IR entry that we will install on the switch...
  ASSERT_OK_AND_ASSIGN(const IrEntities kIrTableEntries,
                       PdTableEntriesToIrEntities(ir_p4info, kPdTableEntries));

  // ...and the translated PI entry that we expect will actually be sent to
  // the switch.
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> kPiEntities,
                       IrEntitiesToPi(ir_p4info, kIrTableEntries));

  p4::v1::Update expected_update;
  expected_update.set_type(p4::v1::Update::INSERT);
  *expected_update.mutable_entity() = kPiEntities.at(0);

  // Expect function to issue `Write` request with IR-to-PI-translated entry.
  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(request.updates(),
                    ElementsAre(EqualsProto(expected_update)));
        return grpc::Status::OK;
      });
  ASSERT_OK(InstallIrEntities(*p4rt_session, kIrTableEntries));
}

TEST(InstallIrEntity, PullsP4InfoFromSwitchAndInstallsIrEntity) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));
  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });
  const p4::v1::Entity kPiEntity = gutil::ParseProtoOrDie<p4::v1::Entity>(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry { multicast_group_id: 42 }
        }
      )pb");
  p4::v1::Update expected_update;
  expected_update.set_type(p4::v1::Update::INSERT);
  *expected_update.mutable_entity() = kPiEntity;
  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(request.updates(),
                    ElementsAre(EqualsProto(expected_update)));
        return grpc::Status::OK;
      });
  // The IR entry that we will install on the switch...
  ASSERT_OK_AND_ASSIGN(const IrEntity kIrEntity,
                       PiEntityToIr(ir_p4info, kPiEntity));
  ASSERT_OK(InstallIrEntity(*p4rt_session, kIrEntity));
}

TEST(DeleteIrEntity, PullsP4InfoFromSwitchAndDeletesIrEntity) {
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));
  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });
  const p4::v1::Entity kPiEntity = gutil::ParseProtoOrDie<p4::v1::Entity>(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry { multicast_group_id: 42 }
        }
      )pb");
  // The IR entry that we will delete from the switch...
  ASSERT_OK_AND_ASSIGN(const IrEntity kIrEntity,
                       PiEntityToIr(ir_p4info, kPiEntity));
  p4::v1::Update expected_update;
  expected_update.set_type(p4::v1::Update::DELETE);
  *expected_update.mutable_entity() = kPiEntity;
  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(request.updates(),
                    ElementsAre(EqualsProto(expected_update)));
        return grpc::Status::OK;
      });
  ASSERT_OK(DeleteIrEntity(*p4rt_session, kIrEntity));
}

TEST(DeletePiEntity, DeletesPiEntity) {
  // Constants.
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));
  const p4::v1::Entity kPiEntity = gutil::ParseProtoOrDie<p4::v1::Entity>(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry { multicast_group_id: 42 }
        }
      )pb");
  // The IR entry that we will delete from the switch...
  ASSERT_OK_AND_ASSIGN(const IrEntity kIrEntity,
                       PiEntityToIr(ir_p4info, kPiEntity));
  p4::v1::Update expected_update;
  expected_update.set_type(p4::v1::Update::DELETE);
  *expected_update.mutable_entity() = kPiEntity;
  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(request.updates(),
                    ElementsAre(EqualsProto(expected_update)));
        return grpc::Status::OK;
      });
  ASSERT_OK(DeletePiEntity(*p4rt_session, kPiEntity));
}

TEST(DeletePiEntities, DeletesPiEntities) {
  // Constants.
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));
  std::vector<p4::v1::Entity> kPiEntities = {
      gutil::ParseProtoOrDie<p4::v1::Entity>(
          R"pb(
            packet_replication_engine_entry {
              multicast_group_entry { multicast_group_id: 1 }
            }
          )pb"),
      gutil::ParseProtoOrDie<p4::v1::Entity>(
          R"pb(
            packet_replication_engine_entry {
              multicast_group_entry { multicast_group_id: 2 }
            }
          )pb"),
      gutil::ParseProtoOrDie<p4::v1::Entity>(
          R"pb(
            table_entry { table_id: 1 }
          )pb"),
  };
  std::vector<p4::v1::Update> expected_updates =
      CreatePiUpdates(kPiEntities, p4::v1::Update::DELETE);

  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(request.updates(),
                    testing::Pointwise(EqualsProto(), expected_updates));
        return grpc::Status::OK;
      });
  ASSERT_OK(DeletePiEntities(*p4rt_session, kPiEntities));
}

TEST(DeleteIrEntities, PullsP4InfoFromSwitchAndDeletesIrEntities) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));
  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });
  pdpi::IrEntities kIrEntities = {
      gutil::ParseProtoOrDie<pdpi::IrEntities>(
          R"pb(
            entities {
              packet_replication_engine_entry {
                multicast_group_entry { multicast_group_id: 1 }
              }
            }
            entities {
              packet_replication_engine_entry {
                multicast_group_entry { multicast_group_id: 2 }
              }
            }
            entities {
              table_entry {
                table_name: "id_test_table"
                matches {
                  name: "ipv6"
                  exact { ipv6: "::ff22" }
                }
                matches {
                  name: "ipv4"
                  exact { ipv4: "16.36.50.82" }
                }
                action {
                  name: "do_thing_1"
                  params {
                    name: "arg2"
                    value { hex_str: "0x00000008" }
                  }
                  params {
                    name: "arg1"
                    value { hex_str: "0x00000009" }
                  }
                }
              }
            }
          )pb"),
  };
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> pi_entities,
                       IrEntitiesToPi(ir_p4info, kIrEntities));
  std::vector<p4::v1::Update> expected_updates =
      CreatePiUpdates(pi_entities, p4::v1::Update::DELETE);
  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(request.updates(),
                    testing::Pointwise(EqualsProto(), expected_updates));
        return grpc::Status::OK;
      });
  ASSERT_OK(DeleteIrEntities(*p4rt_session, kIrEntities));
}

TEST(InstallIrTableEntry, PullsP4InfoFromSwitchAndWritesPdpiTranslatedEntry) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });

  // PD version of our test entry for readability.
  ASSERT_OK_AND_ASSIGN(
      const auto kPdTableEntry,
      gutil::ParseTextProto<pdpi::TableEntry>(
          R"pb(
            ternary_table_entry {
              match { normal { value: "0x0ff" mask: "0x0ff" } }
              action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
              priority: 1
            }
          )pb"));

  // The IR entry that we will install on the switch...
  ASSERT_OK_AND_ASSIGN(
      const IrTableEntry kIrTableEntry,
      PartialPdTableEntryToIrTableEntry(ir_p4info, kPdTableEntry));

  // ...and the translated PI entry that we expect will actually be sent to
  // the switch.
  ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry kPiTableEntry,
                       IrTableEntryToPi(ir_p4info, kIrTableEntry));
  p4::v1::Update expected_update;
  expected_update.set_type(p4::v1::Update::INSERT);
  *expected_update.mutable_entity()->mutable_table_entry() = kPiTableEntry;

  // Expect function to issue `Write` request with IR-to-PI-translated entry.
  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(request.updates(),
                    ElementsAre(EqualsProto(expected_update)));
        return grpc::Status::OK;
      });
  ASSERT_OK(InstallIrTableEntry(*p4rt_session, kIrTableEntry));
}

TEST(InstallPiEntities,
     StringOverloadIssuesWriteRequestInsertingEntitiesToP4rt) {
  const P4Info& p4info = GetTestP4Info();
  // Set up mock P4Runtime session to test against.
  const P4RuntimeSessionOptionalArgs metadata;
  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });

  // Expect `InstallPiEntities` to issue write request inserting given entities.
  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(request.updates(), ElementsAre(EqualsProto(R"pb(
                      type: INSERT
                      entity {
                        packet_replication_engine_entry {
                          multicast_group_entry { multicast_group_id: 42 }
                        }
                      }
                    )pb")));
        return grpc::Status::OK;
      });
  ASSERT_OK(InstallPiEntities(*p4rt_session, R"pb(
    entities {
      packet_replication_engine_entry {
        multicast_group_entry { multicast_group_id: 42 }
      }
    }
  )pb"));
}

TEST(InstallPiEntities,
     ProtoMessageOverloadIssuesWriteRequestInsertingEntitiesToP4rt) {
  const P4Info& p4info = GetTestP4Info();
  // Set up mock P4Runtime session to test against.
  const P4RuntimeSessionOptionalArgs metadata;
  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });

  // Expect `InstallPiEntities` to issue write request inserting given entities.
  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(request.updates(), ElementsAre(EqualsProto(R"pb(
                      type: INSERT
                      entity {
                        packet_replication_engine_entry {
                          multicast_group_entry { multicast_group_id: 42 }
                        }
                      }
                    )pb")));
        return grpc::Status::OK;
      });
  ASSERT_OK(InstallPiEntities(
      *p4rt_session, gutil::ParseProtoOrDie<pdpi::PiEntities>(R"pb(
        entities {
          packet_replication_engine_entry {
            multicast_group_entry { multicast_group_id: 42 }
          }
        }
      )pb")));
}

TEST(InstallPiEntities, SpanOverloadIssuesWriteRequestInsertingEntitiesToP4rt) {
  const P4Info& p4info = GetTestP4Info();
  // Set up mock P4Runtime session to test against.
  const P4RuntimeSessionOptionalArgs metadata;
  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });

  // Expect `InstallPiEntities` to issue write request inserting given entities.
  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(request.updates(), ElementsAre(EqualsProto(R"pb(
                      type: INSERT
                      entity {
                        packet_replication_engine_entry {
                          multicast_group_entry { multicast_group_id: 42 }
                        }
                      }
                    )pb")));
        return grpc::Status::OK;
      });
  ASSERT_OK(InstallPiEntities(
      *p4rt_session, {gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
        packet_replication_engine_entry {
          multicast_group_entry { multicast_group_id: 42 }
        }
      )pb")}));
}

TEST(InstallPiEntities, EntitiesAreSortedByDependency) {
  const P4Info& p4info = GetTestP4Info();
  // Set up mock P4Runtime session to test against.
  const P4RuntimeSessionOptionalArgs metadata;
  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });

  // Expect `InstallPiEntities` to issue write request inserting given entities.
  EXPECT_CALL(mock_p4rt_stub, Write)
      .WillOnce([&](auto, const WriteRequest& request, auto) {
        EXPECT_THAT(
            request.updates(),
            ElementsAre(EqualsProto(R"pb(
                          type: INSERT
                          entity {
                            packet_replication_engine_entry {
                              multicast_group_entry { multicast_group_id: 42 }
                            }
                          }
                        )pb"),
                        EqualsProto(R"pb(
                          type: INSERT
                          entity {
                            table_entry {
                              # refers_to_multicast_by_action table.
                              table_id: 45367444
                              match {
                                field_id: 1
                                exact { value: "\377\"" }
                              }
                              action {
                                action {
                                  action_id: 18598416
                                  params { param_id: 1 value: "42" }
                                }
                              }
                            }
                          }
                        )pb")));
        return grpc::Status::OK;
      });
  // These are in the wrong order, since the reference is before the referee.
  ASSERT_OK(InstallPiEntities(
      *p4rt_session, {gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                        table_entry {
                          # refers_to_multicast_by_action table.
                          table_id: 45367444
                          match {
                            field_id: 1
                            exact { value: "\377\"" }
                          }
                          action {
                            action {
                              action_id: 18598416
                              params { param_id: 1 value: "42" }
                            }
                          }
                        }
                      )pb"),
                      gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                        packet_replication_engine_entry {
                          multicast_group_entry { multicast_group_id: 42 }
                        }
                      )pb")}));
}

TEST(ReadIrEntities, PullsP4InfoFromSwitchAndReadsPdpiTranslatedEntities) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  // The PD versions of the three entities that we will read from the switch.
  // One has a larger-valued priority than another, otherwise equal, entry and
  // should thus be second in the sorted order.
  ASSERT_OK_AND_ASSIGN(
      const auto kPdEntities, gutil::ParseTextProto<pdpi::TableEntries>(R"pb(
        entries {
          ternary_table_entry {
            match { normal { value: "0x0ff" mask: "0x0ff" } }
            action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
            priority: 2
          }
        }
        entries {
          ternary_table_entry {
            match { normal { value: "0x0ff" mask: "0x0ff" } }
            action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
            priority: 1
          }
        }
        entries {
          multicast_group_table_entry {
            match { multicast_group_id: "0x0001" }
            action {
              replicate {
                replicas { port: "1" instance: "0x0001" }
                replicas { port: "2" instance: "0x0002" }
              }
            }
          }
        }
      )pb"));

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // The translated PI entities that we expect will be read from the switch.
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> kPiEntities,
                       PdTableEntriesToPiEntities(ir_p4info, kPdEntities));

  // The IR conversion of the read entities that we expect to get back.
  // Unsorted ReadIrEntities.
  {
    // Expect function to pull P4Info from switch.
    EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
        .WillOnce(
            [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
              *response->mutable_config()->mutable_p4info() = p4info;
              return grpc::Status::OK;
            });
    // Expect function to issue `Read` request that returns 3 PI entities.
    SetNextReadResponse(mock_p4rt_stub, kPiEntities);
    // Expect the call to return OK status with the IR conversion of the read
    // table entries in read order.
    ASSERT_OK_AND_ASSIGN(IrEntities expected_ir_entities_unsorted,
                         PiEntitiesToIr(ir_p4info, kPiEntities));
    // TODO: smolkaj - Use `IgnoringRepeatedFieldOrdering` once that is open
    // source.
    EXPECT_THAT(ReadIrEntities(*p4rt_session),
                IsOkAndHolds(EqualsProto(expected_ir_entities_unsorted)));
  }

  // Sorted ReadIrEntities.
  {
    // Expect function to pull P4Info from switch.
    EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
        .WillOnce(
            [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
              *response->mutable_config()->mutable_p4info() = p4info;
              return grpc::Status::OK;
            });
    // Expect function to issue `Read` request that returns 3 PI entities.
    SetNextReadResponse(mock_p4rt_stub, kPiEntities);
    // Expect the call to return OK status with the IR conversion of the read
    // entities in sorted order.
    ASSERT_OK_AND_ASSIGN(IrEntities expected_ir_entities_sorted,
                         PiEntitiesToIr(ir_p4info, {
                                                       kPiEntities.at(2),
                                                       kPiEntities.at(1),
                                                       kPiEntities.at(0),
                                                   }));
    EXPECT_THAT(ReadIrEntitiesSorted(*p4rt_session),
                IsOkAndHolds(EqualsProto(expected_ir_entities_sorted)));
  }
}

TEST(ReadIrTableEntries, PullsP4InfoFromSwitchAndReadsPdpiTranslatedEntries) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  // The PD versions of the two entries that we will read from the switch.
  // One has a larger-valued priority than the other and should thus be second
  // in the sorted order.
  ASSERT_OK_AND_ASSIGN(
      const auto kPdTableEntries,
      gutil::ParseTextProto<pdpi::TableEntries>(R"pb(
        entries {
          ternary_table_entry {
            match { normal { value: "0x0ff" mask: "0x0ff" } }
            action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
            priority: 2
          }
        }
        entries {
          ternary_table_entry {
            match { normal { value: "0x0ff" mask: "0x0ff" } }
            action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
            priority: 1
          }
        }
      )pb"));

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // The translated PI entries that we expect will be read from the switch.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::TableEntry> kPiTableEntries,
      PartialPdTableEntriesToPiTableEntries(ir_p4info, kPdTableEntries));

  // The IR conversion of the read table entries that we expect to get back.
  // Unsorted ReadIrTableEntries.
  {
    // Expect function to pull P4Info from switch.
    EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
        .WillOnce(
            [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
              *response->mutable_config()->mutable_p4info() = p4info;
              return grpc::Status::OK;
            });
    // Expect function to issue `Read` request that returns 2 PI entries.
    SetNextReadResponse(mock_p4rt_stub, kPiTableEntries);
    // Expect the call to return OK status with the IR conversion of the read
    // table entries in read order.
    ASSERT_OK_AND_ASSIGN(IrTableEntries expected_ir_table_entries_unsorted,
                         PiTableEntriesToIr(ir_p4info, kPiTableEntries));
    EXPECT_THAT(ReadIrTableEntries(*p4rt_session),
                IsOkAndHolds(EqualsProto(expected_ir_table_entries_unsorted)));
  }

  // Sorted ReadIrTableEntries.
  {
    // Expect function to pull P4Info from switch.
    EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
        .WillOnce(
            [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
              *response->mutable_config()->mutable_p4info() = p4info;
              return grpc::Status::OK;
            });
    // Expect function to issue `Read` request that returns 2 PI entries.
    SetNextReadResponse(mock_p4rt_stub, kPiTableEntries);
    // Expect the call to return OK status with the IR conversion of the read
    // table entries in sorted order.
    ASSERT_OK_AND_ASSIGN(
        IrTableEntries expected_ir_table_entries_sorted,
        PiTableEntriesToIr(ir_p4info,
                           {kPiTableEntries.at(1), kPiTableEntries.at(0)}));
    EXPECT_THAT(ReadIrTableEntriesSorted(*p4rt_session),
                IsOkAndHolds(EqualsProto(expected_ir_table_entries_sorted)));
  }
}

TEST(ReadPiEntitiesSorted, GetsSortedEntities) {
  // Constants.
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  // The PD versions of the three entities that we will read from the switch.
  // One has a larger-valued priority than another, otherwise equal, entry and
  // should thus be second in the sorted order.
  ASSERT_OK_AND_ASSIGN(
      const auto kPdTableEntries,
      gutil::ParseTextProto<pdpi::TableEntries>(R"pb(
        entries {
          ternary_table_entry {
            match { normal { value: "0x0ff" mask: "0x0ff" } }
            action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
            priority: 2
          }
        }
        entries {
          ternary_table_entry {
            match { normal { value: "0x0ff" mask: "0x0ff" } }
            action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
            priority: 1
          }
        }
        entries {
          multicast_group_table_entry {
            match { multicast_group_id: "0x0001" }
            action {
              replicate {
                replicas { port: "1" instance: "0x0001" }
                replicas { port: "2" instance: "0x0002" }
              }
            }
          }
        }
      )pb"));

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // The translated PI entities that we expect will be read from the switch.
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> kPiEntities,
                       PdTableEntriesToPiEntities(ir_p4info, kPdTableEntries));
  EXPECT_THAT(kPiEntities, testing::SizeIs(3));

  // Expect function to issue `Read` request that returns PI entities.
  SetNextReadResponse(mock_p4rt_stub, kPiEntities);
  // Expect the call to return OK status with a sorted vector of the read
  // entities.
  EXPECT_THAT(ReadPiEntitiesSorted(*p4rt_session),
              IsOkAndHolds(ElementsAre(EqualsProto(kPiEntities.at(1)),
                                       EqualsProto(kPiEntities.at(0)),
                                       EqualsProto(kPiEntities.at(2)))));
}

TEST(ReadPiTableEntriesSorted, GetsSortedEntities) {
  // Constants.
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  // The PD versions of the two entries that we will read from the switch.
  // One has a larger-valued priority than the other and should thus be second
  // in the sorted order.
  ASSERT_OK_AND_ASSIGN(
      const auto kPdTableEntries,
      gutil::ParseTextProto<pdpi::TableEntries>(R"pb(
        entries {
          ternary_table_entry {
            match { normal { value: "0x0ff" mask: "0x0ff" } }
            action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
            priority: 2
          }
        }
        entries {
          ternary_table_entry {
            match { normal { value: "0x0ff" mask: "0x0ff" } }
            action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
            priority: 1
          }
        }
      )pb"));

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // The translated PI entries that we expect will be read from the switch.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::TableEntry> kPiTableEntries,
      PartialPdTableEntriesToPiTableEntries(ir_p4info, kPdTableEntries));

  // Expect function to issue `Read` request that returns PI entry.
  SetNextReadResponse(mock_p4rt_stub, kPiTableEntries);
  // Expect the call to return OK status with a sorted vector of the read
  // table entries.
  EXPECT_THAT(ReadPiTableEntriesSorted(*p4rt_session),
              IsOkAndHolds(ElementsAre(EqualsProto(kPiTableEntries.at(1)),
                                       EqualsProto(kPiTableEntries.at(0)))));
}

TEST(GetP4Info, GetsConfigAndReturnsErrorIfConfiguredP4InfoIsEmpty) {
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            response->mutable_config()->mutable_p4info();
            return grpc::Status::OK;
          });
  EXPECT_THAT(GetP4Info(*p4rt_session),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}
TEST(GetIrP4Info, GetsConfigAndReturnsErrorIfConfiguredP4InfoIsEmpty) {
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            response->mutable_config()->mutable_p4info();
            return grpc::Status::OK;
          });
  EXPECT_THAT(GetIrP4Info(*p4rt_session),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(GetP4Info, GetsConfigAndReturnsContainedP4InfoIfItisNonEmpty) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });
  EXPECT_THAT(GetP4Info(*p4rt_session), IsOkAndHolds(EqualsProto(p4info)));
}

TEST(GetIrP4Info, GetsConfigAndReturnsContainedP4InfoIfItisNonEmpty) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(
          [&](Unused, Unused, GetForwardingPipelineConfigResponse* response) {
            *response->mutable_config()->mutable_p4info() = p4info;
            return grpc::Status::OK;
          });
  EXPECT_THAT(GetIrP4Info(*p4rt_session), IsOkAndHolds(EqualsProto(ir_p4info)));
}

TEST(GetOrSetP4Info, GetsP4Info) {
  ASSERT_OK_AND_ASSIGN(
      pdpi::P4SessionWithMockStub stub,
      pdpi::MakeP4SessionWithMockStub(pdpi::P4RuntimeSessionOptionalArgs()));

  const p4::config::v1::P4Info existing_p4_info = GetTestP4Info();
  p4::config::v1::P4Info default_p4_info = existing_p4_info;
  default_p4_info.mutable_pkg_info()->add_annotations("@test(default_p4info)");

  p4::v1::GetForwardingPipelineConfigResponse response;
  *response.mutable_config()->mutable_p4info() = existing_p4_info;

  EXPECT_CALL(stub.mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(DoAll(SetArgPointee<2>(response), Return(absl::OkStatus())));
  EXPECT_CALL(stub.mock_p4rt_stub, SetForwardingPipelineConfig).Times(0);

  EXPECT_THAT(GetOrSetP4Info(*stub.p4rt_session, default_p4_info),
              IsOkAndHolds(EqualsProto(existing_p4_info)));
}

TEST(GetOrSetP4Info, SetsP4InfoIfGetIsEmpty) {
  ASSERT_OK_AND_ASSIGN(
      pdpi::P4SessionWithMockStub stub,
      pdpi::MakeP4SessionWithMockStub(pdpi::P4RuntimeSessionOptionalArgs()));

  p4::v1::GetForwardingPipelineConfigResponse response;
  EXPECT_CALL(stub.mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(DoAll(SetArgPointee<2>(response), Return(absl::OkStatus())));

  p4::v1::SetForwardingPipelineConfigRequest set_request;
  EXPECT_CALL(stub.mock_p4rt_stub, SetForwardingPipelineConfig)
      .WillOnce(DoAll(SaveArg<1>(&set_request), Return(absl::OkStatus())));

  const p4::config::v1::P4Info default_p4_info = GetTestP4Info();
  EXPECT_THAT(GetOrSetP4Info(*stub.p4rt_session, default_p4_info),
              IsOkAndHolds(EqualsProto(default_p4_info)));
  EXPECT_THAT(set_request.config().p4info(), EqualsProto(default_p4_info));
}

TEST(GetOrSetP4Info, ReturnsErrorIfGetFails) {
  ASSERT_OK_AND_ASSIGN(
      pdpi::P4SessionWithMockStub stub,
      pdpi::MakeP4SessionWithMockStub(pdpi::P4RuntimeSessionOptionalArgs()));

  EXPECT_CALL(stub.mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(Return(absl::UnknownError("error")));

  const p4::config::v1::P4Info default_p4_info = GetTestP4Info();
  EXPECT_THAT(GetOrSetP4Info(*stub.p4rt_session, default_p4_info), Not(IsOk()));
}

TEST(GetOrSetP4Info, ReturnsErrorIfSetFails) {
  ASSERT_OK_AND_ASSIGN(
      pdpi::P4SessionWithMockStub stub,
      pdpi::MakeP4SessionWithMockStub(pdpi::P4RuntimeSessionOptionalArgs()));
  EXPECT_CALL(stub.mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(stub.mock_p4rt_stub, SetForwardingPipelineConfig)
      .WillOnce(Return(absl::UnknownError("error")));

  const p4::config::v1::P4Info default_p4_info = GetTestP4Info();
  EXPECT_THAT(GetOrSetP4Info(*stub.p4rt_session, default_p4_info), Not(IsOk()));
}

// Takes number of entries to test with as parameter.
class SendPiUpdatesAndReturnPerUpdateStatusTest
    : public testing::TestWithParam<int> {};

TEST_P(SendPiUpdatesAndReturnPerUpdateStatusTest,
       SendsValidRequestAndReturnsValidResponse) {
  // Constants.
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  std::vector<p4::v1::Update> updates;
  p4::v1::WriteRequest expected_request;
  pdpi::IrWriteRpcStatus returned_status;
  // Regardless of how many updates we send, we should always get an rpc
  // response.
  returned_status.mutable_rpc_response();
  for (int i = 1; i < GetParam(); ++i) {
    // Construct PD version and translated PI version of entry that we write to
    // the switch.
    ASSERT_OK_AND_ASSIGN(
        const auto pd_entry,
        gutil::ParseTextProto<pdpi::TableEntry>(absl::Substitute(
            R"pb(
              ternary_table_entry {
                match { normal { value: "0x0ff" mask: "0x0ff" } }
                action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
                priority: $0
              }
            )pb",
            i)));
    ASSERT_OK_AND_ASSIGN(
        const p4::v1::TableEntry pi_entry,
        PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry));

    // Construct updates and add them both to the vector we use as function
    // input and in the write request we expect the function to send.
    p4::v1::Update& update = updates.emplace_back();
    update.set_type(p4::v1::Update::INSERT);
    *update.mutable_entity()->mutable_table_entry() = pi_entry;
    *expected_request.add_updates() = update;
    // All updates we send are OK.
    returned_status.mutable_rpc_response()->add_statuses()->set_code(
        google::rpc::OK);
  }

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Set write request metadata.
  expected_request.set_device_id(p4rt_session->DeviceId());
  expected_request.set_role(p4rt_session->Role());
  *expected_request.mutable_election_id() = p4rt_session->ElectionId();

  // Test SendPiUpdatesAndReturnPerUpdateStatus with an absl::Span of updates.
  {
    // Expect function to issue `Write` request with IR-to-PI-translated entry.
    EXPECT_CALL(mock_p4rt_stub, Write)
        .WillOnce([&](auto, const WriteRequest& request, auto) {
          EXPECT_THAT(request, EqualsProto(expected_request));
          return grpc::Status::OK;
        });
    EXPECT_THAT(SendPiUpdatesAndReturnPerUpdateStatus(*p4rt_session, updates),
                IsOkAndHolds(EqualsProto(returned_status)));
  }
  // Test SendPiUpdatesAndReturnPerUpdateStatus with a RepeatedPtrField.
  {
    // Expect function to issue `Write` request with IR-to-PI-translated entry.
    EXPECT_CALL(mock_p4rt_stub, Write)
        .WillOnce([&](auto, const WriteRequest& request, auto) {
          EXPECT_THAT(request, EqualsProto(expected_request));
          return grpc::Status::OK;
        });
    EXPECT_THAT(SendPiUpdatesAndReturnPerUpdateStatus(
                    *p4rt_session, expected_request.updates()),
                IsOkAndHolds(EqualsProto(returned_status)));
  }
}

INSTANTIATE_TEST_SUITE_P(SendsValidRequestAndReturnsValidResponse,
                         SendPiUpdatesAndReturnPerUpdateStatusTest,
                         testing::ValuesIn(/*num_entries=*/{0, 1, 5}),
                         [](const testing::TestParamInfo<int>& info) {
                           return absl::StrCat("With", info.param, "Entries");
                         });

}  // namespace
}  // namespace pdpi

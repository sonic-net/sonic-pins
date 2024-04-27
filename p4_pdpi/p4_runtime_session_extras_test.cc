#include "p4_pdpi/p4_runtime_session_extras.h"

#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"

#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session_mocking.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_pdpi/testing/test_p4info.h"

namespace pdpi {
namespace {

using ::gutil::EqualsProto;
using ::p4::config::v1::P4Info;
using ::p4::v1::GetForwardingPipelineConfigResponse;
using ::p4::v1::WriteRequest;
using ::testing::ElementsAre;

using ::testing::status::IsOkAndHolds;

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
  ASSERT_OK_AND_ASSIGN(const std::vector<p4::v1::TableEntry> kPiTableEntries,
                       PdTableEntriesToPi(ir_p4info, kPdTableEntries));
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
            [&](auto, auto, GetForwardingPipelineConfigResponse* response) {
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
            [&](auto, auto, GetForwardingPipelineConfigResponse* response) {
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
  ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry kPiTableEntry,
                       PdTableEntryToPi(ir_p4info, kPdTableEntry));
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
            [&](auto, auto, GetForwardingPipelineConfigResponse* response) {
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
            [&](auto, auto, GetForwardingPipelineConfigResponse* response) {
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

TEST(ReadIrTableEntries, PullsP4InfoFromSwitchAndReadsPdpiTranslatedEntries) {
  // Constants.
  const P4Info& p4info = GetTestP4Info();
  const IrP4Info& ir_p4info = GetTestIrP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  // The PD version of the entry that we will read from the switch.
  ASSERT_OK_AND_ASSIGN(
      const auto kPdTableEntry, gutil::ParseTextProto<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match { normal { value: "0x0ff" mask: "0x0ff" } }
          action { do_thing_3 { arg1: "0xffffffff" arg2: "0xffffffff" } }
          priority: 1
        }
      )pb"));

  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Expect function to pull P4Info from switch.
  EXPECT_CALL(mock_p4rt_stub, GetForwardingPipelineConfig)
      .WillOnce([&](auto, auto, GetForwardingPipelineConfigResponse* response) {
        *response->mutable_config()->mutable_p4info() = p4info;
        return grpc::Status::OK;
      });

  // The translated PI entry that we expect will be read from the switch.
  ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry kPiTableEntry,
                       PdTableEntryToPi(ir_p4info, kPdTableEntry));
  // Expect function to issue `Read` request that returns PI entry.
  SetNextReadResponse(mock_p4rt_stub, {kPiTableEntry});
  // Expect the call to return OK status with the IR conversion of the read
  // table entry.
  ASSERT_OK_AND_ASSIGN(IrTableEntry expected_ir_table_entry,
                       PiTableEntryToIr(ir_p4info, kPiTableEntry));
  EXPECT_THAT(ReadIrTableEntries(*p4rt_session),
              IsOkAndHolds(ElementsAre(EqualsProto(expected_ir_table_entry))));
}

}  // namespace
}  // namespace pdpi

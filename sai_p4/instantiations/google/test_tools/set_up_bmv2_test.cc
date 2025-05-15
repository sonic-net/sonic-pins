#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"

#include <vector>

#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {

namespace {

struct TestParams {
  // The flavor of SAI P4 to be tested. The test should pass for all
  // instantiations.
  sai::Instantiation instantiation;
  // Whether to preload BMv2 with a clone configuration.
  InitialBmv2ControlPlane initial_bmv2_control_plane;
};

std::vector<TestParams> GetTestParams() {
  std::vector<TestParams> params;
  for (const auto& instantiation : sai::AllSaiInstantiations()) {
    for (auto config_type : {InitialBmv2ControlPlane::kInstallCloneEntries,
                             InitialBmv2ControlPlane::kNoControlPlane}) {
      params.emplace_back() = TestParams{
          .instantiation = instantiation,
          .initial_bmv2_control_plane = config_type,
      };
    }
  }
  return params;
}

class SetUpBmv2Test : public testing::TestWithParam<TestParams> {};

TEST_P(SetUpBmv2Test, CloneEntriesAreInstalledCorrectly) {
  ASSERT_OK_AND_ASSIGN(
      orion::p4::test::Bmv2 bmv2,
      SetUpBmv2ForSaiP4(GetParam().instantiation,
                        {
                            .initial_bmv2_control_plane =
                                GetParam().initial_bmv2_control_plane,
                        },
                        DefaultSaiP4Bmv2Args()));

  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  read_request.add_entities()
      ->mutable_packet_replication_engine_entry()
      ->mutable_clone_session_entry();
  read_request.add_entities()
      ->mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response,
                       pdpi::SetMetadataAndSendPiReadRequest(
                           &bmv2.P4RuntimeSession(), read_request));

  // The instance of the BMv2 SAI program should hold the initial clone
  // configuration, if kInstallCloneEntries is set. Otherwise no entry should be
  // present.
  switch (GetParam().initial_bmv2_control_plane) {
    case InitialBmv2ControlPlane::kInstallCloneEntries:
      // There are over 1000 clone entries.
      // So we just make sure that there is at least one entry present.
      EXPECT_GT(read_response.entities_size(), 0);
      break;
    case InitialBmv2ControlPlane::kNoControlPlane:
      EXPECT_EQ(read_response.entities_size(), 0);
      break;
    default:
      FAIL() << "Unknown initial BMv2 control plane type: "
             << absl::StrCat(GetParam().initial_bmv2_control_plane);
  }
}

INSTANTIATE_TEST_SUITE_P(SetUpBmv2, SetUpBmv2Test,
                         testing::ValuesIn(GetTestParams()),
                         [](const auto& test) {
                           return absl::StrFormat(
                               "%v_%v", test.param.instantiation,
                               test.param.initial_bmv2_control_plane);
                         });

}  // namespace
}  // namespace sai

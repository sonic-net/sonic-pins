#include "lib/ixia_protocol_helper.h"

#include <string_view>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "lib/utils/json_test_utils.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/mock_generic_testbed.h"

namespace pins_test::ixia {
namespace {

using ::gutil::IsOkAndHolds;
using ::pins_test::JsonIs;
using ::testing::Return;

TEST(LacpIxiahHelperTest, CreateLag) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kPost, "/ixnetwork/lag",
                  JsonIs(R"json({"vports": ["/vport/1", "/vport/2"]})json")))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/lag/1"}]})json"}));
    EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(thinkit::RequestType::kPost,
                            "/api/v1/sessions/1/ixnetwork/lag/1/protocolStack",
                            /*payload=*/""))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/lag/1/protocolStack"}]})json"}));
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kPost,
                  "/api/v1/sessions/1/ixnetwork/lag/1/protocolStack/ethernet",
                  /*payload=*/""))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/lag/1/protocolStack/ethernet/1"}]})json"}));
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(thinkit::RequestType::kPost,
                                    "/api/v1/sessions/1/ixnetwork/lag/1/"
                                    "protocolStack/ethernet/1/lagportlacp",
                                    /*payload=*/""))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/lag/1/protocolStack/ethernet/1/lagportlacp/1"}]})json"}));
  EXPECT_THAT(CreateLag({"/vport/1", "/vport/2"}, mock_generic_testbed),
              IsOkAndHolds("/api/v1/sessions/1/ixnetwork/lag/1"));
}

TEST(LacpIxiahHelperTest, CreateTopology) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(thinkit::RequestType::kPost, "/ixnetwork/topology",
                            JsonIs(R"json({"ports": ["/lag/1"]})json")))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/topology/1"}]})json"}));
  EXPECT_THAT(CreateTopology("/lag/1", mock_generic_testbed),
              IsOkAndHolds("/api/v1/sessions/1/ixnetwork/topology/1"));
}

TEST(LacpIxiahHelperTest, CreateDeviceGroup) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(thinkit::RequestType::kPost,
                                    "/ixnetwork/topology/1/deviceGroup",
                                    JsonIs(R"json({"multiplier": 1})json")))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/topology/1/deviceGroup/1"}]})json"}));
  EXPECT_THAT(
      CreateDeviceGroup("/ixnetwork/topology/1", mock_generic_testbed),
      IsOkAndHolds("/api/v1/sessions/1/ixnetwork/topology/1/deviceGroup/1"));
}

TEST(LacpIxiahHelperTest, AddEthernetProtocol) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(thinkit::RequestType::kPost,
                            "/ixnetwork/topology/1/deviceGroup/1/ethernet",
                            /*payload=*/""))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/topology/1/deviceGroup/1/ethernet/1"}]})json"}));
  EXPECT_THAT(
      AddEthernetProtocol("/ixnetwork/topology/1/deviceGroup/1",
                          mock_generic_testbed),
      IsOkAndHolds(
          "/api/v1/sessions/1/ixnetwork/topology/1/deviceGroup/1/ethernet/1"));
}

TEST(LacpIxiahHelperTest, AddIpv4Protocol) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kPost,
                  "/ixnetwork/topology/1/deviceGroup/1/ethernet/1/ipv4",
                  /*payload=*/""))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/topology/1/deviceGroup/1/ethernet/1/ipv4/1"}]})json"}));
  EXPECT_THAT(AddIpv4Protocol("/ixnetwork/topology/1/deviceGroup/1/ethernet/1",
                              mock_generic_testbed),
              IsOkAndHolds("/api/v1/sessions/1/ixnetwork/topology/1/"
                           "deviceGroup/1/ethernet/1/ipv4/1"));
}

TEST(LacpIxiahHelperTest, StartAllProtocols) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(thinkit::RequestType::kPost,
                                    "/ixnetwork/operations/startallprotocols",
                                    /*payload=*/""))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 200, .response = R"json({"state":"SUCCESS"})json"}));
  EXPECT_OK(StartAllProtocols(mock_generic_testbed));
}

}  // namespace
}  // namespace pins_test::ixia

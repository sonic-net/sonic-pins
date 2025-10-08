#include "lib/ixia_protocol_helper.h"

#include <string>
#include <string_view>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/substitute.h"
#include "absl/types/span.h"
#include "gutil/status.h"
#include "lib/ixia_helper.h"
#include "thinkit/generic_testbed.h"

namespace pins_test::ixia {
namespace {

constexpr std::string_view kLagPath = "/ixnetwork/lag";
constexpr std::string_view kTopologyPath = "/ixnetwork/topology";
constexpr std::string_view kStartAllProtocolsPath =
    "/ixnetwork/operations/startallprotocols";

}  // namespace

absl::StatusOr<std::string> CreateLag(absl::Span<const std::string> vports,
                                      thinkit::GenericTestbed& testbed) {
  std::string payload = absl::Substitute(R"json({"vports":["$0"]})json",
                                         absl::StrJoin(vports, R"(",")"));
  ASSIGN_OR_RETURN(thinkit::HttpResponse response,
                   testbed.SendRestRequestToIxia(thinkit::RequestType::kPost,
                                                 kLagPath, payload));
  if (response.response_code != 201) {
    return absl::InternalError(
        absl::StrCat("Failed to create LAG: ", response.response));
  }
  ASSIGN_OR_RETURN(std::string lag_href, ExtractHref(response));

  // Add LACP protocol to the LAG.
  ASSIGN_OR_RETURN(
      response, testbed.SendRestRequestToIxia(
                    thinkit::RequestType::kPost,
                    absl::StrCat(lag_href, "/protocolStack"), /*payload=*/""));
  if (response.response_code != 201) {
    return absl::InternalError(absl::StrCat(
        "Failed to add protocol stack to LAG: ", response.response));
  }
  ASSIGN_OR_RETURN(
      response,
      testbed.SendRestRequestToIxia(
          thinkit::RequestType::kPost,
          absl::StrCat(lag_href, "/protocolStack/ethernet"), /*payload=*/""));
  if (response.response_code != 201) {
    return absl::InternalError(
        absl::StrCat("Failed to add Ethernet to LAG: ", response.response));
  }
  ASSIGN_OR_RETURN(
      response,
      testbed.SendRestRequestToIxia(
          thinkit::RequestType::kPost,
          absl::StrCat(lag_href, "/protocolStack/ethernet/1/lagportlacp"),
          /*payload=*/""));
  if (response.response_code != 201) {
    return absl::InternalError(
        absl::StrCat("Failed to add LACP to LAG: ", response.response));
  }
  return lag_href;
}

absl::StatusOr<std::string> CreateTopology(std::string_view port,
                                           thinkit::GenericTestbed& testbed) {
  std::string payload = absl::Substitute(R"json({"ports":["$0"]})json", port);
  ASSIGN_OR_RETURN(thinkit::HttpResponse response,
                   testbed.SendRestRequestToIxia(thinkit::RequestType::kPost,
                                                 kTopologyPath, payload));
  if (response.response_code != 201) {
    return absl::InternalError(
        absl::StrCat("Failed to create LAG: ", response.response));
  }
  return ExtractHref(response);
}

absl::StatusOr<std::string> CreateDeviceGroup(
    std::string_view topology, thinkit::GenericTestbed& testbed) {
  std::string path = absl::StrCat(topology, "/deviceGroup");
  ASSIGN_OR_RETURN(
      thinkit::HttpResponse response,
      testbed.SendRestRequestToIxia(thinkit::RequestType::kPost, path,
                                    R"json({"multiplier": 1})json"));
  if (response.response_code != 201) {
    return absl::InternalError(
        absl::StrCat("Failed to create device group: ", response.response));
  }
  return ExtractHref(response);
}

absl::StatusOr<std::string> AddEthernetProtocol(
    std::string_view device_group, thinkit::GenericTestbed& testbed) {
  std::string path = absl::StrCat(device_group, "/ethernet");
  ASSIGN_OR_RETURN(
      thinkit::HttpResponse response,
      testbed.SendRestRequestToIxia(thinkit::RequestType::kPost, path,
                                    /*payload=*/""));
  if (response.response_code != 201) {
    return absl::InternalError(
        absl::StrCat("Failed to add ethernet protocol: ", response.response));
  }
  return ExtractHref(response);
}

absl::StatusOr<std::string> AddIpv4Protocol(std::string_view ethernet_protocol,
                                            thinkit::GenericTestbed& testbed) {
  std::string path = absl::StrCat(ethernet_protocol, "/ipv4");
  ASSIGN_OR_RETURN(
      thinkit::HttpResponse response,
      testbed.SendRestRequestToIxia(thinkit::RequestType::kPost, path,
                                    /*payload=*/""));
  if (response.response_code != 201) {
    return absl::InternalError(
        absl::StrCat("Failed to add IPv4 protocol: ", response.response));
  }
  return ExtractHref(response);
}

absl::Status StartAllProtocols(thinkit::GenericTestbed& testbed) {
  return SendAndWaitForComplete(kStartAllProtocolsPath, /*payload=*/"",
                                testbed);
}

}  // namespace pins_test::ixia

// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "lib/ixia_helper.h"

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "google/protobuf/struct.pb.h"
#include "gutil/collections.h"
#include "gutil/overload.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.pb.h"
#include "lib/utils/json_utils.h"
#include "thinkit/generic_testbed.h"

namespace pins_test::ixia {

using Json = nlohmann::json;
using ::json_yang::FormatJsonBestEffort;

absl::StatusOr<int> FindIdByField(const thinkit::HttpResponse &response,
                                  absl::string_view field,
                                  absl::string_view desired_value) {
  ASSIGN_OR_RETURN(Json array, json_yang::ParseJson(response.response));
  if (!array.is_array()) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Response is not an array:\n", json_yang::DumpJson(array)));
  }
  std::string field_to_find(field);
  for (const auto &[_, element] : array.items()) {
    if (json_yang::GetSimpleJsonValueAsString(element[field_to_find]) !=
        desired_value) {
      continue;
    }
    Json id = element["id"];
    if (!id.is_number_integer()) {
      return absl::InternalError(
          absl::StrCat("'id' is not an integer: ", id.dump()));
    }
    return id.get<int>();
  }
  return absl::NotFoundError(
      absl::StrCat("Response does not contain the desired element (", field,
                   ": ", desired_value, "):\n", json_yang::DumpJson(array)));
}

// ExtractHref - Extract the href path from the Ixia response.
// An example response:
// {"links":[{"rel":"self","method":"GET","href":"/api/v1/sessions/82/ixnetwork/availableHardware/chassis/1"}]}
// which in this case would return
// href = /api/v1/sessions/82/ixnetwork/availableHardware/chassis/1
//
absl::StatusOr<std::string> ExtractHref(thinkit::HttpResponse &resp) {
  std::string href = "";
  Json config_json = Json::parse(resp.response);
  auto inner_json = config_json["links"];
  if (inner_json.empty()) return absl::InternalError("no links");
  auto first_json = inner_json[0];
  if (first_json.empty()) return absl::InternalError("no inner");
  for (const auto &el : first_json.items()) {
    if (el.key() == "href") {
      href = el.value();
      break;
    }
  }
  if (href.empty()) return absl::InternalError("no href");
  return href;
}

// Extract ip, card and port from a fully qualified ixia interface name.
absl::StatusOr<IxiaPortInfo> ExtractPortInfo(absl::string_view ixia_interface) {
  std::vector<absl::string_view> interface_attributes =
      absl::StrSplit(ixia_interface, '/');
  if (interface_attributes.size() != 3) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected interface name with 3 parts separated by `/` but found "
           << interface_attributes.size() << " parts for interface "
           << ixia_interface;
  }

  return IxiaPortInfo{
      .hostname = std::string(interface_attributes[0]),
      .card = std::string(interface_attributes[1]),
      .port = std::string(interface_attributes[2]),
  };
}

// IxiaConnect - connect to the Ixia.  returns the href from the response
// or an error.
absl::StatusOr<std::string> IxiaConnect(
    absl::string_view ixia_ip, thinkit::GenericTestbed &generic_testbed) {
  std::string chassis_path = "/ixnetwork/availableHardware/chassis";
  std::string chassis_json = absl::StrCat("[{\"hostname\":\"", ixia_ip, "\"}]");
  LOG(INFO) << "path " << chassis_path;
  LOG(INFO) << "json " << chassis_json;

  // This seems to take about 35 seconds, works after increasing RPC timeout
  // default to two minutes.
  ASSIGN_OR_RETURN(
      thinkit::HttpResponse chassis_response,
      generic_testbed.SendRestRequestToIxia(thinkit::RequestType::kPost,
                                            chassis_path, chassis_json));

  LOG(INFO) << "Received code " << chassis_response.response_code;
  LOG(INFO) << "Received response "
            << FormatJsonBestEffort(chassis_response.response);
  if (chassis_response.response_code != 201)
    return absl::InternalError(absl::StrFormat("unexpected response %d: %s",
                                               chassis_response.response_code,
                                               chassis_response.response));

  // Extract the href path from the response and return it.
  ASSIGN_OR_RETURN(std::string href, ExtractHref(chassis_response));
  return href;
}

absl::StatusOr<std::string> IxiaVport(
    absl::string_view href,
    absl::string_view fully_qualified_ixia_interface_name,
    thinkit::GenericTestbed &generic_testbed) {
  ASSIGN_OR_RETURN(IxiaPortInfo port_info,
                   ExtractPortInfo(fully_qualified_ixia_interface_name));
  return IxiaVport(href, port_info.card, port_info.port, generic_testbed);
}

// IxiaVport - Connect to an Ixia Card/Port.  Returns either an error or the
// href string from the response.
absl::StatusOr<std::string> IxiaVport(
    absl::string_view href, absl::string_view ixia_card,
    absl::string_view ixia_port, thinkit::GenericTestbed &generic_testbed) {
  // Post to
  // /ixnetwork/availableHardware/chassis/card/port/operations/clearownership
  // with:
  // [{"arg1":"/api/v1/sessions/1/ixnetwork/availableHardware/chassis/1/card/9/port/1"},]
  // to clear ownership for card 9 port 1
  std::string clear_path =
      "/ixnetwork/availableHardware/chassis/card/port/operations/"
      "clearownership";
  std::string clear_json = absl::StrCat("{\"arg1\":[\"", href, "/card/",
                                        ixia_card, "/port/", ixia_port, "\"]}");
  LOG(INFO) << "path " << clear_path;
  LOG(INFO) << "json " << clear_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse clear_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPost, clear_path, clear_json));

  // Post to ixnetwork/vport with:
  // [{"connectedTo":"/api/v1/sessions/1/ixnetwork/availableHardware/chassis/1/card/9/port/1"},]
  // to reserve card 9 port 1
  std::string connected_path = "/ixnetwork/vport";
  std::string connected_json =
      absl::StrCat("[{\"connectedTo\":\"", href, "/card/", ixia_card, "/port/",
                   ixia_port, "\"},]");
  LOG(INFO) << "path " << connected_path;
  LOG(INFO) << "json " << connected_json;
  ASSIGN_OR_RETURN(
      thinkit::HttpResponse connected_response,
      generic_testbed.SendRestRequestToIxia(thinkit::RequestType::kPost,
                                            connected_path, connected_json));

  LOG(INFO) << "Received code " << connected_response.response_code;
  LOG(INFO) << "Received response "
            << FormatJsonBestEffort(connected_response.response);
  if (connected_response.response_code != 201)
    return absl::InternalError(absl::StrFormat("unexpected response %d: %s",
                                               connected_response.response_code,
                                               connected_response.response));

  ASSIGN_OR_RETURN(std::string vref, ExtractHref(connected_response));

  return vref;
}

// IxiaSession - starts an Ixia session.  Returns either an error or the
// href string for the first traffic item, e.g. something like
// "/api/v1/sessions/101/ixnetwork/traffic/trafficItem/1"
absl::StatusOr<std::string> IxiaSession(
    absl::string_view vref, thinkit::GenericTestbed &generic_testbed) {
  // POST to /traffic/trafficItem with:
  // [{"name":"Unicast Traffic"}]
  std::string traffic_path = "/ixnetwork/traffic/trafficItem";
  std::string traffic_json = "[{\"name\":\"Unicast Traffic\"}]";
  LOG(INFO) << "path " << traffic_path;
  LOG(INFO) << "json " << traffic_json;
  ASSIGN_OR_RETURN(
      thinkit::HttpResponse traffic_response,
      generic_testbed.SendRestRequestToIxia(thinkit::RequestType::kPost,
                                            traffic_path, traffic_json));

  LOG(INFO) << "Received code " << traffic_response.response_code;
  LOG(INFO) << "Received response "
            << FormatJsonBestEffort(traffic_response.response);
  if (traffic_response.response_code != 201)
    return absl::InternalError(absl::StrFormat("unexpected response %d: %s",
                                               traffic_response.response_code,
                                               traffic_response.response));

  // something like
  // {"links":[{"rel":"self","method":"GET","href":"/api/v1/sessions/101/ixnetwork/traffic/trafficItem/1"}]}
  // and we need to extract /ixnetwork/traffic/trafficItem/1 for use
  ASSIGN_OR_RETURN(std::string tref, ExtractHref(traffic_response));
  LOG(INFO) << "tref = " << tref;

  // POST to /ixnetwork/traffic/trafficItem/1/endpointSet with
  // [{"sources":["/api/v1/sessions/1/ixnetwork/vport/2/protocols"]}]
  std::string endp_path = tref + "/endpointSet";
  std::string endp_json =
      absl::StrCat("[{\"sources\":[\"", vref, "/protocols\"]}]");
  LOG(INFO) << "path " << endp_path;
  LOG(INFO) << "json " << endp_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse endp_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPost, endp_path, endp_json));

  LOG(INFO) << "Received code " << endp_response.response_code;
  LOG(INFO) << "Received response "
            << FormatJsonBestEffort(endp_response.response);
  if (endp_response.response_code != 201)
    return absl::InternalError(absl::StrFormat("unexpected response %d: %s",
                                               endp_response.response_code,
                                               endp_response.response));

  return tref;
}

absl::StatusOr<std::string> SetUpTrafficItem(
    absl::string_view vref_src, absl::string_view vref_dst,
    thinkit::GenericTestbed &generic_testbed) {
  absl::BitGen gen;
  std::string traffic_name = absl::StrCat(vref_src, " -> ", vref_dst, " ",
                                          absl::Uniform<uint32_t>(gen));
  return SetUpTrafficItem(vref_src, vref_dst, traffic_name, generic_testbed);
}

// SetupTrafficItem - Sets up a traffic item with source and destination port.
// Returns either an error or the
// href string for the first traffic item, e.g. something like
// "/api/v1/sessions/101/ixnetwork/traffic/trafficItem/1"
absl::StatusOr<std::string> SetUpTrafficItem(
    absl::string_view vref_src, absl::string_view vref_dst,
    absl::string_view traffic_name, thinkit::GenericTestbed &generic_testbed) {
  // POST to /traffic/trafficItem with:
  // [{"name":"Unicast Traffic"}]
  constexpr absl::string_view kTrafficPath = "/ixnetwork/traffic/trafficItem";
  const Json kTrafficJson = Json::array({
      Json::object({{"name", traffic_name}}),
  });
  LOG(INFO) << "path " << kTrafficPath;
  LOG(INFO) << "json " << kTrafficJson;
  ASSIGN_OR_RETURN(
      thinkit::HttpResponse traffic_response,
      generic_testbed.SendRestRequestToIxia(thinkit::RequestType::kPost,
                                            kTrafficPath, kTrafficJson.dump()));
  LOG(INFO) << "Received code " << traffic_response.response_code;
  LOG(INFO) << "Received response "
            << FormatJsonBestEffort(traffic_response.response);
  if (traffic_response.response_code != 201)
    return absl::InternalError(absl::StrFormat("unexpected response %d: %s",
                                               traffic_response.response_code,
                                               traffic_response.response));

  // something like
  // {"links":[{"rel":"self","method":"GET","href":"/api/v1/sessions/101/ixnetwork/traffic/trafficItem/1"}]}
  // and we need to extract /ixnetwork/traffic/trafficItem/1 for use
  ASSIGN_OR_RETURN(std::string tref, ExtractHref(traffic_response));
  LOG(INFO) << "tref = " << tref;

  // POST to /ixnetwork/traffic/trafficItem/1/endpointSet with
  // [{"sources":["/api/v1/sessions/1/ixnetwork/vport/2/protocols"]}]
  std::string endp_path = tref + "/endpointSet";
  std::string endp_json = absl::StrCat("[{\"sources\":[\"", vref_src,
                                       "/protocols\"],\"destinations\":[\"",
                                       vref_dst, "/protocols\"]}]");
  LOG(INFO) << "path " << endp_path;
  LOG(INFO) << "json " << endp_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse endp_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPost, endp_path, endp_json));
  LOG(INFO) << "Received code " << endp_response.response_code;
  LOG(INFO) << "Received response "
            << FormatJsonBestEffort(endp_response.response);
  if (endp_response.response_code != 201) {
    return absl::InternalError(absl::StrFormat("unexpected response %d: %s",
                                               endp_response.response_code,
                                               endp_response.response));
  }

  std::string trackby_path = tref + "/tracking";
  std::string trackby_json = "{\"trackBy\":[\"flowGroup0\"]}";
  LOG(INFO) << "path " << trackby_path;
  LOG(INFO) << "json " << trackby_json;
  ASSIGN_OR_RETURN(
      thinkit::HttpResponse trackby_response,
      generic_testbed.SendRestRequestToIxia(thinkit::RequestType::kPatch,
                                            trackby_path, trackby_json));

  LOG(INFO) << "Received code " << trackby_response.response_code;
  LOG(INFO) << "Received response "
            << FormatJsonBestEffort(trackby_response.response);
  if (trackby_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response %d: %s",
                                               trackby_response.response_code,
                                               trackby_response.response));

  return tref;
}

absl::Status DeleteTrafficItem(absl::string_view tref,
                               thinkit::GenericTestbed &testbed) {
  StopTraffic(tref, testbed).IgnoreError();
  LOG(INFO) << "Sending DELETE to '" << tref << "'";
  ASSIGN_OR_RETURN(
      thinkit::HttpResponse response,
      testbed.SendRestRequestToIxia(thinkit::RequestType::kDelete, tref, ""));
  LOG(INFO) << "Received code " << response.response_code;
  LOG(INFO) << "Received response " << FormatJsonBestEffort(response.response);
  if (response.response_code == 200) return absl::OkStatus();
  return gutil::InternalErrorBuilder() << "unexpected response: " << response;
}

// WaitForComplete - If 202 returned, check for IN_PROGRESS and if so poll
//                   returned url until complete
//
// An example response:
// {"id":"","url":"","resultUrl":"","executionTimeMs":57.0,"state":"SUCCESS","progress":100,"message":null,"result":"kVoid"}
//
absl::Status WaitForComplete(const thinkit::HttpResponse &response,
                             thinkit::GenericTestbed &generic_testbed,
                             absl::Duration timeout) {
  LOG(INFO) << "Returns " << response.response_code;
  LOG(INFO) << "Returns " << response.response;

  if (response.response_code == 200) return absl::OkStatus();

  if (response.response_code != 202)
    return absl::InternalError(
        absl::StrFormat("unexpected response: %d", response.response_code));

  Json resp_json = Json::parse(response.response);
  Json state_json = resp_json["state"];
  if (state_json.empty()) return absl::InternalError("no state");
  std::string state = state_json.get<std::string>();
  LOG(INFO) << "state = " << state;
  if (state == "SUCCESS") {
    LOG(INFO) << "state is success";
    return absl::OkStatus();
  }

  if (state != "IN_PROGRESS")
    return absl::InternalError(absl::StrFormat("unexpected state %s", state));

  Json url_json = resp_json["url"];
  if (url_json.empty()) return absl::InternalError("no url");
  std::string url = url_json.get<std::string>();

  // allow up to a minute for the state to resolve
  absl::Time t1 = absl::Now();

  while (1) {
    ASSIGN_OR_RETURN(thinkit::HttpResponse get_response,
                     generic_testbed.SendRestRequestToIxia(
                         thinkit::RequestType::kGet, url, ""));

    if (get_response.response_code != 200)
      return absl::InternalError(absl::StrFormat("unexpected response: %d",
                                                 get_response.response_code));

    LOG(INFO) << "Get (poll) returns " << get_response.response_code;
    LOG(INFO) << "Get (poll) returns " << get_response.response;

    resp_json = Json::parse(get_response.response);
    state_json = resp_json["state"];
    if (state_json.empty()) return absl::InternalError("no state");
    state = state_json.get<std::string>();
    LOG(INFO) << "state = " << state;
    if (state == "SUCCESS") {
      break;
    }

    if (absl::Now() >= t1 + timeout)
      return absl::DeadlineExceededError("Poll limit expired");
  }

  LOG(INFO) << "polling is complete";
  return absl::OkStatus();
}

absl::Status StartTraffic(absl::string_view tref, absl::string_view href,
                          thinkit::GenericTestbed &generic_testbed) {
  return StartTraffic(std::vector<std::string>{std::string(tref)}, href,
                      generic_testbed);
}

absl::Status StartTraffic(absl::Span<const std::string> trefs,
                          absl::string_view href,
                          thinkit::GenericTestbed &generic_testbed) {
  LOG(INFO) << "\n\n\n\n\n---------- Starting... ----------\n\n\n\n\n";

  // Extract IxRef from href which is the substring ending at /ixnetwork
  static constexpr absl::string_view kIxRefUrlComponent = "/ixnetwork";
  auto ixpos = href.find(kIxRefUrlComponent);
  if (ixpos == absl::string_view::npos) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid href since 'ixnetwork' substring was not found which is "
              "needed to extract the Ixia chassis URL portion from href "
           << href;
  }

  absl::string_view ixref = href.substr(0, ixpos + kIxRefUrlComponent.size());

  // Start the process of getting the traffic flowing.
  // POST to /ixnetwork/traffic/trafficItem/operations/generate with
  // {"arg1":["/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1",
  // "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/2"]}
  std::string generate_path =
      "/ixnetwork/traffic/trafficItem/operations/generate";
  std::string generate_json =
      absl::StrCat(R"({"arg1":[")", absl::StrJoin(trefs, R"(",")"), R"("]})");
  LOG(INFO) << "path " << generate_path;
  LOG(INFO) << "json " << generate_json;
  ASSIGN_OR_RETURN(
      thinkit::HttpResponse generate_response,
      generic_testbed.SendRestRequestToIxia(thinkit::RequestType::kPost,
                                            generate_path, generate_json));
  // Returns something like
  // {"id":"","url":"","resultUrl":"","executionTimeMs":57.0,"state":"SUCCESS","progress":100,"message":null,"result":"kVoid"}
  RETURN_IF_ERROR(WaitForComplete(generate_response, generic_testbed));

  // POST to /ixnetwork/traffic/operations/apply with
  // {"arg1":"/api/v1/sessions/1/ixnetwork/traffic"}
  std::string apply_path = "/ixnetwork/traffic/operations/apply";
  std::string apply_json = absl::StrCat("{\"arg1\":\"", ixref, "/traffic\"}");
  LOG(INFO) << "path " << apply_path;
  LOG(INFO) << "json " << apply_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse apply_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPost, apply_path, apply_json));
  // returns something like:
  // {"id":"","url":"","resultUrl":"","executionTimeMs":111.0,"state":"ERROR","progress":100,"message":null,"result":"Error
  // in L2/L3 Traffic Apply\n"}
  RETURN_IF_ERROR(WaitForComplete(generate_response, generic_testbed));

  // POST to
  // /ixnetwork/traffic/trafficItem/operations/startstatelesstrafficblocking
  // with  {"arg1":["/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1",
  // "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/2"]}
  std::string start_path =
      "/ixnetwork/traffic/trafficItem/operations/startstatelesstrafficblocking";
  std::string start_json =
      absl::StrCat(R"({"arg1":[")", absl::StrJoin(trefs, R"(",")"), R"("]})");
  LOG(INFO) << "path " << start_path;
  LOG(INFO) << "json " << start_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse start_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPost, start_path, start_json));
  RETURN_IF_ERROR(WaitForComplete(start_response, generic_testbed));

  // GET to /ixnetwork/traffic/trafficItem
  std::string titem_path = "/ixnetwork/traffic/trafficItem";
  LOG(INFO) << "path " << titem_path;
  ASSIGN_OR_RETURN(thinkit::HttpResponse titem_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kGet, titem_path, ""));
  LOG(INFO) << "Received code " << titem_response.response_code;
  LOG(INFO) << "Received response "
            << FormatJsonBestEffort(titem_response.response);

  // Check for warnings.
  ASSIGN_OR_RETURN(Json response,
                   json_yang::ParseJson(titem_response.response));
  RET_CHECK(response.is_array()) << titem_response;
  for (const Json &traffic_item : response) {
    RET_CHECK(traffic_item.contains("errors")) << titem_response;
    RET_CHECK(traffic_item.contains("warnings")) << titem_response;
    if (!traffic_item.at("errors").empty()) {
      return gutil::UnknownErrorBuilder()
             << "Found traffic items with errors, which may result in "
                "unexpected behavior. Dump of traffic items:\n"
             << json_yang::DumpJson(response);
    }
    if (!traffic_item.at("warnings").empty()) {
      LOG(INFO)
          << "WARNING: Found traffic items with warnings, which may result in "
             "unexpected behavior. Dump of traffic items:\n"
          << json_yang::DumpJson(response);
    }
  }

  return absl::OkStatus();
}

absl::Status StopTraffic(absl::string_view tref,
                         thinkit::GenericTestbed &generic_testbed) {
  return StopTraffic(std::vector<std::string>{std::string(tref)},
                     generic_testbed);
}

absl::Status StopTraffic(absl::Span<const std::string> trefs,
                         thinkit::GenericTestbed &generic_testbed) {
  LOG(INFO) << "\n\n\n\n\n---------- Stopping... ----------\n\n\n\n\n";

  // POST to
  // /ixnetwork/traffic/trafficItem/operations/stopstatelesstrafficblocking with
  // {"arg1":["/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1",
  // "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/2"]}
  std::string stop_path =
      "/ixnetwork/traffic/trafficItem/operations/stopstatelesstrafficblocking";
  std::string stop_json =
      absl::StrCat(R"({"arg1":[")", absl::StrJoin(trefs, R"(",")"), R"("]})");
  LOG(INFO) << "path " << stop_path;
  LOG(INFO) << "json " << stop_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse stop_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPost, stop_path, stop_json));
  RETURN_IF_ERROR(WaitForComplete(stop_response, generic_testbed));

  LOG(INFO) << "\n\n\n\n\n---------- Stopped ----------\n\n\n\n\n";
  return absl::OkStatus();
}

absl::Status SetFrameRate(absl::string_view tref, int64_t fps,
                          thinkit::GenericTestbed &generic_testbed) {
  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1/frameRate
  // with {"rate":NNN,"type":"framesPerSecond"}
  std::string rate_path = absl::StrCat(tref, "/configElement/1/frameRate");
  std::string rate_json =
      absl::StrCat("{\"rate\":", fps, ",\"type\":\"framesPerSecond\"}");
  LOG(INFO) << "path " << rate_path;
  LOG(INFO) << "json " << rate_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse rate_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, rate_path, rate_json));
  LOG(INFO) << "Returns " << rate_response.response_code;
  if (rate_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response: %u",
                                               rate_response.response_code));
  return absl::OkStatus();
}

absl::Status SetLineRate(absl::string_view tref, int32_t percent,
                         thinkit::GenericTestbed &generic_testbed) {
  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1/frameRate
  // with {"rate":NNN,"type":"percentLineRate"}
  std::string rate_path = absl::StrCat(tref, "/configElement/1/frameRate");
  std::string rate_json =
      absl::StrCat("{\"rate\":", percent, ",\"type\":\"percentLineRate\"}");
  LOG(INFO) << "path " << rate_path;
  LOG(INFO) << "json " << rate_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse rate_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, rate_path, rate_json));
  LOG(INFO) << "Returns " << rate_response.response_code;
  if (rate_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response: %u",
                                               rate_response.response_code));
  return absl::OkStatus();
}

absl::Status SetFrameCount(absl::string_view tref, int64_t frames,
                           thinkit::GenericTestbed &generic_testbed) {
  // Set the transmissionControl type to fixed count and the frame count
  // to NNN
  // PATCH to
  // /ixnetwork/traffic/trafficItem/1/configElement/1/transmissionControl
  // with {"type":"fixedFrameCount","frameCount","NNN"}
  std::string fixed_path =
      absl::StrCat(tref, "/configElement/1/transmissionControl");
  std::string fixed_json = absl::StrCat(
      "{\"type\":\"fixedFrameCount\",\"frameCount\":\"", frames, "\"}");
  LOG(INFO) << "path " << fixed_path;
  LOG(INFO) << "json " << fixed_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse fixed_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, fixed_path, fixed_json));
  LOG(INFO) << "Returns " << fixed_response.response_code;
  if (fixed_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response: %u",
                                               fixed_response.response_code));
  return absl::OkStatus();
}

absl::Status SetFrameSize(absl::string_view tref, int32_t framesize,
                          thinkit::GenericTestbed &generic_testbed) {
  // Set the frame size to 1514 bytes
  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1/frameSize
  // with {"fixedSize":"NNNN"}
  std::string size_path = absl::StrCat(tref, "/configElement/1/frameSize");
  std::string size_json = absl::StrCat("{\"fixedSize\":", framesize, "}");
  LOG(INFO) << "path " << size_path;
  LOG(INFO) << "json " << size_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse size_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, size_path, size_json));
  LOG(INFO) << "Returns " << size_response.response_code;
  if (size_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response: %u",
                                               size_response.response_code));
  return absl::OkStatus();
}

absl::Status SetDestMac(absl::string_view tref, absl::string_view dmac,
                        thinkit::GenericTestbed &generic_testbed) {
  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1/stack/1/field/1
  // with {"singleValue":"xx:xx:xx:xx:xx:xx"} to set the destination MAC
  std::string dmac_path =
      absl::StrCat(tref, "/configElement/1/stack/1/field/1");
  std::string dmac_json = absl::StrCat("{\"singleValue\":\"", dmac, "\"}");
  LOG(INFO) << "path " << dmac_path;
  LOG(INFO) << "json " << dmac_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse dmac_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, dmac_path, dmac_json));
  LOG(INFO) << "Returns " << dmac_response.response_code;
  if (dmac_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response: %u",
                                               dmac_response.response_code));
  return absl::OkStatus();
}

absl::Status SetSrcMac(absl::string_view tref, absl::string_view smac,
                       thinkit::GenericTestbed &generic_testbed) {
  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1/stack/1/field/2
  // with {"singleValue":"xx:xx:xx:xx:xx:xx"} to set the source MAC
  std::string smac_path =
      absl::StrCat(tref, "/configElement/1/stack/1/field/2");
  std::string smac_json = absl::StrCat("{\"singleValue\":\"", smac, "\"}");
  LOG(INFO) << "path " << smac_path;
  LOG(INFO) << "json " << smac_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse smac_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, smac_path, smac_json));
  LOG(INFO) << "Returns " << smac_response.response_code;
  if (smac_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response: %u",
                                               smac_response.response_code));
  return absl::OkStatus();
}

absl::Status AppendIPv4(absl::string_view tref,
                        thinkit::GenericTestbed &generic_testbed) {
  // GET to /ixnetwork/traffic/protocolTemplate to find the correct protocol
  // template to use for IPv4 traffic
  std::string proto_path =
      "/ixnetwork/traffic/protocolTemplate?links=true&skip=0&take=end";
  LOG(INFO) << "path " << proto_path;
  ASSIGN_OR_RETURN(thinkit::HttpResponse proto_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kGet, proto_path, ""));
  LOG(INFO) << "Received code " << proto_response.response_code;
  LOG(INFO) << "Received response "
            << FormatJsonBestEffort(proto_response.response);
  if (proto_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response: %u",
                                               proto_response.response_code));
  // LOG(INFO) << "Returns " << proto_response.response;
  // we're looking for this one:
  // {"id":333,"displayName":"IPv4","stackTypeId":"ipv4","templateName":"ipv4-template.xml","links":[{"rel":"child","method":"GET","href":"/api/v1/sessions/84/ixnetwork/traffic/protocolTemplate/333/field"}
  // and we want to extract the href but without the /field part.
  std::size_t ixname = proto_response.response.find("\"displayName\":\"IPv4\"");
  if (ixname == std::string::npos)
    return absl::InternalError("no IPv4 template");
  std::size_t ixhref = proto_response.response.find("\"href\":", ixname);
  if (ixhref == std::string::npos)
    return absl::InternalError("no IPv4 template(2)");
  std::size_t ixqt = proto_response.response.find('"', ixhref + 8);
  if (ixqt == std::string::npos)
    return absl::InternalError("no IPv4 template(3)");
  std::string ipref =
      proto_response.response.substr(ixhref + 8, ixqt - ixhref - 8);
  std::size_t ixfield = ipref.find("/field");
  if (ixfield != std::string::npos) {
    ipref = ipref.substr(0, ixfield);
  }
  LOG(INFO) << "ipref = " << ipref;

  // POST to
  // /ixnetwork/traffic/trafficItem/configElement/stack/operations/appendprotocol
  // {"arg1":"/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/configElement/1/stack/1","arg2":"/api/v1/sessions/1/ixnetwork/traffic/protocolTemplate/330"}
  std::string append_path =
      "/ixnetwork/traffic/trafficItem/configElement/stack/operations/"
      "appendprotocol";
  std::string append_json =
      absl::StrCat("{\"arg1\":\"", tref,
                   "/configElement/1/stack/1\",\"arg2\":\"", ipref, "\"}");
  LOG(INFO) << "path " << append_path;
  LOG(INFO) << "json " << append_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse append_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPost, append_path, append_json));
  LOG(INFO) << "Received code: " << append_response.response_code;
  LOG(INFO) << "Received response: "
            << FormatJsonBestEffort(append_response.response);
  return WaitForComplete(append_response, generic_testbed);
}

absl::Status SetSrcIPv4(absl::string_view tref, absl::string_view sip,
                        thinkit::GenericTestbed &generic_testbed) {
  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1/stack/2/field/27
  // with {"singleValue":"X.X.X.X"} to set the source IP addres
  std::string sip_path =
      absl::StrCat(tref, "/configElement/1/stack/2/field/27");
  std::string sip_json = absl::StrCat("{\"singleValue\":\"", sip, "\"}");
  LOG(INFO) << "path " << sip_path;
  LOG(INFO) << "json " << sip_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse sip_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, sip_path, sip_json));
  LOG(INFO) << "Returns " << sip_response.response_code;
  if (sip_response.response_code != 200)
    return absl::InternalError(
        absl::StrFormat("unexpected response: %u", sip_response.response_code));
  return absl::OkStatus();
}

absl::Status SetDestIPv4(absl::string_view tref, absl::string_view dip,
                         thinkit::GenericTestbed &generic_testbed) {
  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1/stack/2/field/28
  // with {"singleValue":"X.X.X.X"} to set the destination IP addres
  std::string dip_path =
      absl::StrCat(tref, "/configElement/1/stack/2/field/28");
  std::string dip_json = absl::StrCat("{\"singleValue\":\"", dip, "\"}");
  LOG(INFO) << "path " << dip_path;
  LOG(INFO) << "json " << dip_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse dip_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, dip_path, dip_json));
  LOG(INFO) << "Returns " << dip_response.response_code;
  if (dip_response.response_code != 200)
    return absl::InternalError(
        absl::StrFormat("unexpected response: %u", dip_response.response_code));
  return absl::OkStatus();
}

absl::Status AppendIPv6(absl::string_view tref,
                        thinkit::GenericTestbed &generic_testbed) {
  // GET to /ixnetwork/traffic/protocolTemplate to find the correct protocol
  // template to use for IPv6 traffic
  std::string proto_path =
      "/ixnetwork/traffic/protocolTemplate?links=true&skip=0&take=end";
  LOG(INFO) << "path " << proto_path;
  ASSIGN_OR_RETURN(thinkit::HttpResponse proto_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kGet, proto_path, ""));
  LOG(INFO) << "Returns " << proto_response.response_code;
  if (proto_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response: %u",
                                               proto_response.response_code));
  // LOG(INFO) << "Returns " << proto_response.response;
  // we're looking for this one:
  // {"id":334,"displayName":"IPv6","stackTypeId":"ipv6","templateName":"ipv6-template.xml","links":[{"rel":"child","method":"GET","href":"/api/v1/sessions/84/ixnetwork/traffic/protocolTemplate/334/field"},
  // and we want to extract the href but without the /field part.
  std::size_t ixname = proto_response.response.find("\"displayName\":\"IPv6\"");
  if (ixname == std::string::npos)
    return absl::InternalError("no IPv6 template");
  std::size_t ixhref = proto_response.response.find("\"href\":", ixname);
  if (ixhref == std::string::npos)
    return absl::InternalError("no IPv6 template(2)");
  std::size_t ixqt = proto_response.response.find('"', ixhref + 8);
  if (ixqt == std::string::npos)
    return absl::InternalError("no IPv6 template(3)");
  std::string ipref =
      proto_response.response.substr(ixhref + 8, ixqt - ixhref - 8);
  std::size_t ixfield = ipref.find("/field");
  if (ixfield != std::string::npos) {
    ipref = ipref.substr(0, ixfield);
  }
  LOG(INFO) << "ipref = " << ipref;

  // POST to
  // /ixnetwork/traffic/trafficItem/configElement/stack/operations/appendprotocol
  // {"arg1":"/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/configElement/1/stack/1","arg2":"/api/v1/sessions/1/ixnetwork/traffic/protocolTemplate/330"}
  std::string append_path =
      "/ixnetwork/traffic/trafficItem/configElement/stack/operations/"
      "appendprotocol";

  std::string append_json =
      absl::StrCat("{\"arg1\":\"", tref,
                   "/configElement/1/stack/1\",\"arg2\":\"", ipref, "\"}");
  LOG(INFO) << "path " << append_path;
  LOG(INFO) << "json " << append_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse append_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPost, append_path, append_json));
  LOG(INFO) << "Received code: " << append_response.response_code;
  LOG(INFO) << "Received response: "
            << FormatJsonBestEffort(append_response.response);
  return ixia::WaitForComplete(append_response, generic_testbed);
}

absl::Status SetSrcIPv6(absl::string_view tref, absl::string_view sip,
                        thinkit::GenericTestbed &generic_testbed) {
  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1/stack/2/field/7
  // with {"singleValue":"fe80::201:02ff:fe03:0405"} to set the source IPv6
  // address
  std::string sip_path = absl::StrCat(tref, "/configElement/1/stack/2/field/7");
  std::string sip_json = absl::StrCat("{\"singleValue\":\"", sip, "\"}");
  LOG(INFO) << "path " << sip_path;
  LOG(INFO) << "json " << sip_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse sip_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, sip_path, sip_json));
  LOG(INFO) << "Returns " << sip_response.response_code;
  if (sip_response.response_code != 200)
    return absl::InternalError(
        absl::StrFormat("unexpected response: %u", sip_response.response_code));
  return absl::OkStatus();
}

absl::Status SetDestIPv6(absl::string_view tref, absl::string_view dip,
                         thinkit::GenericTestbed &generic_testbed) {
  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1/stack/2/field/8
  // with {"singleValue":"fe80::002:02ff:fe02:0202"} to set the dest IPv6
  // address
  std::string dip_path = absl::StrCat(tref, "/configElement/1/stack/2/field/8");
  std::string dip_json = absl::StrCat("{\"singleValue\":\"", dip, "\"}");
  LOG(INFO) << "path " << dip_path;
  LOG(INFO) << "json " << dip_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse dip_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, dip_path, dip_json));
  LOG(INFO) << "Returns " << dip_response.response_code;
  if (dip_response.response_code != 200)
    return absl::InternalError(
        absl::StrFormat("unexpected response: %u", dip_response.response_code));
  return absl::OkStatus();
}

absl::Status SetIpPriority(absl::string_view tref, int dscp, int ecn_bits,
                           bool is_ipv4,
                           thinkit::GenericTestbed &generic_testbed) {
  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1/stack/2/field/3
  // with {"singleValue":"10/00"} to enable or disable ECN.

  if (dscp < 0 || dscp > 63) {
    return absl::InvalidArgumentError(
        absl::StrFormat("Invalid dscp: %d, valid range 0 - 63", dscp));
  }

  if (ecn_bits < 0 || ecn_bits > 3) {
    return absl::InvalidArgumentError(
        absl::StrFormat("Invalid ecn_bits: %d, valid range 0 - 3", dscp));
  }

  std::string sip_path =
      is_ipv4 ? absl::StrCat(tref, "/configElement/1/stack/2/field/3")
              : absl::StrCat(tref, "/configElement/1/stack/2/field/2");

  // Ixia REST nuance:
  // IPv4 header accepts TOS field in hex but IPv6 header accepts TOS field
  // in decimal.
  std::string sip_json;
  if (is_ipv4) {
    sip_json =
        absl::StrCat("{\"activeFieldChoice\":true,\"singleValue\":\"",
                     absl::StrFormat("%X", (dscp << 2) | (ecn_bits)), "\"}");
  } else {
    sip_json =
        absl::StrCat("{\"activeFieldChoice\":true,\"singleValue\":\"",
                     absl::StrFormat("%d", (dscp << 2) | (ecn_bits)), "\"}");
  }

  LOG(INFO) << "path " << sip_path;
  LOG(INFO) << "json " << sip_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse sip_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, sip_path, sip_json));
  LOG(INFO) << "Returns " << sip_response.response_code;
  if (sip_response.response_code != 200)
    return absl::InternalError(
        absl::StrFormat("unexpected response: %u", sip_response.response_code));
  return absl::OkStatus();
}

absl::Status SetIpTTL(absl::string_view tref, int ttl, bool is_ipv4,
                      thinkit::GenericTestbed &generic_testbed) {
  if (ttl < 0 || ttl > 64) {
    return absl::InvalidArgumentError(
        absl::StrFormat("Invalid ttl: %d, valid range 0 - 64", ttl));
  }

  std::string sip_path =
      is_ipv4 ? absl::StrCat(tref, "/configElement/1/stack/2/field/24")
              : absl::StrCat(tref, "/configElement/1/stack/2/field/6");

  std::string sip_json;

  sip_json = absl::StrCat("{\"activeFieldChoice\":true,\"singleValue\":\"",
                          absl::StrFormat("%d", ttl), "\"}");

  LOG(INFO) << "path " << sip_path;
  LOG(INFO) << "json " << sip_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse sip_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, sip_path, sip_json));
  LOG(INFO) << "Returns " << sip_response.response_code;
  if (sip_response.response_code != 200)
    return absl::InternalError(
        absl::StrFormat("unexpected response: %u", sip_response.response_code));
  return absl::OkStatus();
}

absl::Status AppendTcp(absl::string_view tref,
                       thinkit::GenericTestbed &generic_testbed) {
  // GET to /ixnetwork/traffic/protocolTemplate to find the correct protocol
  // template to use for TCP traffic.
  constexpr absl::string_view kProtoPath =
      "/ixnetwork/traffic/protocolTemplate?links=true&skip=0&take=end";
  ASSIGN_OR_RETURN(thinkit::HttpResponse proto_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kGet, kProtoPath, ""));
  LOG(INFO) << "Returns " << proto_response.response_code;
  if (proto_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response: %u",
                                               proto_response.response_code));

  std::size_t ixname = proto_response.response.find("\"displayName\":\"TCP\"");
  if (ixname == std::string::npos)
    return absl::InternalError("no TCP template");
  std::size_t ixhref = proto_response.response.find("\"href\":", ixname);
  if (ixhref == std::string::npos)
    return absl::InternalError("no TCP template(2)");
  std::size_t ixqt = proto_response.response.find('"', ixhref + 8);
  if (ixqt == std::string::npos)
    return absl::InternalError("no TCP template(3)");
  std::string tcpref =
      proto_response.response.substr(ixhref + 8, ixqt - ixhref - 8);
  std::size_t ixfield = tcpref.find("/field");
  if (ixfield != std::string::npos) {
    tcpref = tcpref.substr(0, ixfield);
  }

  // POST to
  // /ixnetwork/traffic/trafficItem/configElement/stack/operations/appendprotocol
  // {"arg1":"/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/configElement/1/stack/1","arg2":"/api/v1/sessions/1/ixnetwork/traffic/protocolTemplate/<template>"}
  std::string append_path =
      "/ixnetwork/traffic/trafficItem/configElement/stack/operations/"
      "appendprotocol";

  std::string append_json =
      absl::StrCat("{\"arg1\":\"", tref,
                   "/configElement/1/stack/2\",\"arg2\":\"", tcpref, "\"}");
  LOG(INFO) << "path " << append_path;
  LOG(INFO) << "json " << append_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse append_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPost, append_path, append_json));
  LOG(INFO) << "Received code: " << append_response.response_code;
  LOG(INFO) << "Received response: "
            << FormatJsonBestEffort(append_response.response);
  return ixia::WaitForComplete(append_response, generic_testbed);
}

absl::Status AppendUdp(absl::string_view tref,
                       thinkit::GenericTestbed &generic_testbed) {
  // GET to /ixnetwork/traffic/protocolTemplate to find the correct protocol
  // template to use for UDP traffic.
  constexpr absl::string_view kProtoPath =
      "/ixnetwork/traffic/protocolTemplate?links=true&skip=0&take=end";
  ASSIGN_OR_RETURN(thinkit::HttpResponse proto_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kGet, kProtoPath, ""));
  LOG(INFO) << "Returns " << proto_response.response_code;
  if (proto_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response: %u",
                                               proto_response.response_code));

  std::size_t ixname = proto_response.response.find("\"displayName\":\"UDP\"");
  if (ixname == std::string::npos)
    return absl::InternalError("no UDP template");
  std::size_t ixhref = proto_response.response.find("\"href\":", ixname);
  if (ixhref == std::string::npos)
    return absl::InternalError("no UDP template(2)");
  std::size_t ixqt = proto_response.response.find('"', ixhref + 8);
  if (ixqt == std::string::npos)
    return absl::InternalError("no UDP template(3)");
  std::string tcpref =
      proto_response.response.substr(ixhref + 8, ixqt - ixhref - 8);
  std::size_t ixfield = tcpref.find("/field");
  if (ixfield != std::string::npos) {
    tcpref = tcpref.substr(0, ixfield);
  }

  // POST to
  // /ixnetwork/traffic/trafficItem/configElement/stack/operations/appendprotocol
  // {"arg1":"/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/configElement/1/stack/1","arg2":"/api/v1/sessions/1/ixnetwork/traffic/protocolTemplate/<template>"}
  constexpr absl::string_view kAppendPath =
      "/ixnetwork/traffic/trafficItem/configElement/stack/operations/"
      "appendprotocol";

  std::string append_json =
      absl::StrCat("{\"arg1\":\"", tref,
                   "/configElement/1/stack/2\",\"arg2\":\"", tcpref, "\"}");
  LOG(INFO) << "json " << append_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse append_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPost, kAppendPath, append_json));
  LOG(INFO) << "Received code: " << append_response.response_code;
  LOG(INFO) << "Received response: "
            << FormatJsonBestEffort(append_response.response);
  return ixia::WaitForComplete(append_response, generic_testbed);
}

absl::Status AppendProtocolAtStack(absl::string_view tref,
                                   absl::string_view protocol,
                                   absl::string_view stack,
                                   thinkit::GenericTestbed &generic_testbed) {
  // GET to /ixnetwork/traffic/protocolTemplate to find the correct protocol
  // template to use.
  constexpr absl::string_view kProtoPath =
      "/ixnetwork/traffic/protocolTemplate?links=true&skip=0&take=end";
  ASSIGN_OR_RETURN(thinkit::HttpResponse proto_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kGet, kProtoPath, ""));
  LOG(INFO) << "Returns " << proto_response.response_code;
  if (proto_response.response_code != 200)
    return absl::InternalError(absl::StrFormat("unexpected response: %u",
                                               proto_response.response_code));

  std::size_t ixname = proto_response.response.find(
      absl::Substitute("\"displayName\":\"$0\"", protocol));
  if (ixname == std::string::npos)
    return absl::InternalError(
        absl::StrCat("no template found for ", protocol));
  std::size_t ixhref = proto_response.response.find("\"href\":", ixname);
  if (ixhref == std::string::npos)
    return absl::InternalError(
        absl::StrCat("no template found for ", protocol));
  std::size_t ixqt = proto_response.response.find('"', ixhref + 8);
  if (ixqt == std::string::npos)
    return absl::InternalError(
        absl::StrCat("no template found for ", protocol));
  std::string tcpref =
      proto_response.response.substr(ixhref + 8, ixqt - ixhref - 8);
  std::size_t ixfield = tcpref.find("/field");
  if (ixfield != std::string::npos) {
    tcpref = tcpref.substr(0, ixfield);
  }

  // POST to
  // /ixnetwork/traffic/trafficItem/configElement/stack/operations/appendprotocol
  // {"arg1":"/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/configElement/1/stack/<stack>","arg2":"/api/v1/sessions/1/ixnetwork/traffic/protocolTemplate/<template>"}
  constexpr absl::string_view kAppendPath =
      "/ixnetwork/traffic/trafficItem/configElement/stack/operations/"
      "appendprotocol";

  std::string append_json =
      absl::StrCat("{\"arg1\":\"", tref, "/configElement/1/stack/", stack,
                   "\",\"arg2\":\"", tcpref, "\"}");
  LOG(INFO) << "json " << append_json;
  ASSIGN_OR_RETURN(thinkit::HttpResponse append_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPost, kAppendPath, append_json));
  LOG(INFO) << "Received code: " << append_response.response_code;
  LOG(INFO) << "Received response: "
            << FormatJsonBestEffort(append_response.response);
  return ixia::WaitForComplete(append_response, generic_testbed);
}

absl::StatusOr<std::string> GetRawStatsView(
    absl::string_view href, int stats_view_index,
    thinkit::GenericTestbed &generic_testbed) {
  // Extract IxRef from href which is the substring ending at /ixnetwork
  static constexpr absl::string_view kIxRefUrlComponent = "/ixnetwork";
  auto ixpos = href.find(kIxRefUrlComponent);
  if (ixpos == absl::string_view::npos) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid href since 'ixnetwork' substring was not found which is "
              "needed to extract the Ixia chassis URL portion from href "
           << href;
  }

  absl::string_view ixref = href.substr(0, ixpos + kIxRefUrlComponent.size());

  std::string stats_view_path =
      absl::StrCat(ixref, "/statistics/view/", stats_view_index, "/data");
  LOG(INFO) << "path " << stats_view_path;
  ASSIGN_OR_RETURN(thinkit::HttpResponse stat_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kGet, stats_view_path, ""));
  LOG(INFO) << "Received code: " << stat_response.response_code;
  LOG(INFO) << "Received response: "
            << FormatJsonBestEffort(stat_response.response);
  return stat_response.response;
}

// Parses time stamp in format `hh:mm:ss.xx` as seconds.
static absl::StatusOr<double> ParseTimeStampAsSeconds(
    absl::string_view timestamp, absl::string_view description) {
  absl::Time time_since_unix_epoch;
  if (!absl::ParseTime("%H:%M:%E*S", timestamp, &time_since_unix_epoch,
                       /*err=*/nullptr)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "expected time stamp of the form hh:mm:ss.xx, but got: '"
           << timestamp << "'";
  }
  return absl::ToDoubleSeconds(time_since_unix_epoch - absl::UnixEpoch());
}

static absl::StatusOr<int64_t> ParseInt64(absl::string_view value,
                                          absl::string_view description) {
  int64_t result;
  if (absl::SimpleAtoi(value, &result)) return result;
  return gutil::InvalidArgumentErrorBuilder()
         << "cannot parse '" << description << "' value '" << value
         << "' as int64_t";
}

absl::StatusOr<TrafficStats> ParseTrafficItemStats(
    absl::string_view raw_stats) {
  TrafficStats result;

  // Let proto google::protobuf's json_util do the heavy lifting.
  ASSIGN_OR_RETURN(StatsViewObject stats_proto,
                   gutil::ParseJsonAsProto<StatsViewObject>(
                       raw_stats, /*ignore_unknown_fields=*/true));
  if (!stats_proto.is_ready()) {
    return gutil::UnavailableErrorBuilder() << "stats not ready yet";
  }

  for (auto &[row_name, row] : stats_proto.row_values()) {
    if (row.values_size() != 1 || !row.values(0).has_list_value()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "row '" << row_name
             << "' of stats view object has unexpected format";
    }
    const google::protobuf::ListValue &values = row.values(0).list_value();
    if (values.values_size() != stats_proto.column_captions_size()) {
      if (stats_proto.column_captions_size() == 0 ||
          values.values_size() == 0) {
        return gutil::UnavailableErrorBuilder() << "stats not ready yet";
      }
      return gutil::InvalidArgumentErrorBuilder()
             << "found " << stats_proto.column_captions_size()
             << " column captions, but " << values.values_size()
             << " values in row '" << row_name << "'";
    }

    // Organize values by their caption.
    absl::flat_hash_map<std::string, std::string> value_by_caption;
    for (int i = 0; i < values.values_size(); ++i) {
      const google::protobuf::Value &value = values.values(i);
      if (value.kind_case() != google::protobuf::Value::kStringValue) {
        return gutil::InvalidArgumentErrorBuilder()
               << "expected string value, but found: " << value.DebugString();
      }
      value_by_caption[stats_proto.column_captions(i)] =
          values.values(i).string_value();
    }

    // Extract the values we are interested in.
    ASSIGN_OR_RETURN(const std::string name,
                     gutil::FindOrStatus(value_by_caption, "Traffic Item"));
    TrafficItemStats &parsed_row =
        (*result.mutable_stats_by_traffic_item())[name];
    parsed_row.set_traffic_item_name(name);
    ASSIGN_OR_RETURN(*parsed_row.mutable_tx_port(),
                     gutil::FindOrStatus(value_by_caption, "Tx Port"));
    ASSIGN_OR_RETURN(*parsed_row.mutable_rx_port(),
                     gutil::FindOrStatus(value_by_caption, "Rx Port"));
    {
      ASSIGN_OR_RETURN(std::string raw,
                       gutil::FindOrStatus(value_by_caption, "Tx Frames"));
      ASSIGN_OR_RETURN(auto value, ParseInt64(raw, "Tx Frames"));
      parsed_row.set_num_tx_frames(value);
    }
    {
      ASSIGN_OR_RETURN(std::string raw,
                       gutil::FindOrStatus(value_by_caption, "Rx Frames"));
      ASSIGN_OR_RETURN(auto value, ParseInt64(raw, "Rx Frames"));
      parsed_row.set_num_rx_frames(value);
    }
    {
      ASSIGN_OR_RETURN(std::string raw,
                       gutil::FindOrStatus(value_by_caption, "Rx Bytes"));
      ASSIGN_OR_RETURN(auto value, ParseInt64(raw, "Rx Bytes"));
      parsed_row.set_rx_bytes(value);
    }
    {
      ASSIGN_OR_RETURN(std::string raw, gutil::FindOrStatus(value_by_caption,
                                                            "First TimeStamp"));
      if (raw.empty()) {
        return gutil::UnavailableErrorBuilder()
               << "'First TimeStamp' not available yet";
      }
      ASSIGN_OR_RETURN(auto value,
                       ParseTimeStampAsSeconds(raw, "First TimeStamp"));
      parsed_row.set_first_time_stamp(value);
    }
    {
      ASSIGN_OR_RETURN(std::string raw,
                       gutil::FindOrStatus(value_by_caption, "Last TimeStamp"));
      ASSIGN_OR_RETURN(auto value,
                       ParseTimeStampAsSeconds(raw, "Last TimeStamp"));
      parsed_row.set_last_time_stamp(value);
    }
  }

  return result;
}

absl::StatusOr<TrafficStats> GetAllTrafficItemStats(
    absl::string_view href, thinkit::GenericTestbed &generic_testbed) {
  ASSIGN_OR_RETURN(thinkit::HttpResponse views,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kGet, "/ixnetwork/statistics/view",
                       /*payload=*/""));
  ASSIGN_OR_RETURN(int traffic_item_stats_index,
                   FindIdByField(views, "caption", "Flow Statistics"));
  // It takes some time for stats to become "ready", so we have to poll.
  // TODO: Do not hardcode this.
  constexpr absl::Duration kPollDuration = absl::Minutes(2);
  const absl::Time kTimeout = absl::Now() + kPollDuration;
  while (absl::Now() < kTimeout) {
    ASSIGN_OR_RETURN(
        std::string raw_stats,
        GetRawStatsView(href, traffic_item_stats_index, generic_testbed));
    absl::StatusOr<TrafficStats> stats = ParseTrafficItemStats(raw_stats);
    if (absl::IsUnavailable(stats.status())) {
      absl::SleepFor(absl::Seconds(1));
      continue;  // Stats not ready yet, try again.
    } else {
      RETURN_IF_ERROR(stats.status()).SetAppend()
          << "\nwhile trying to parse the following stats:\n"
          << FormatJsonBestEffort(raw_stats);
    }
    LOG(INFO) << "Stats ready after "
              << absl::Now() - (kTimeout - kPollDuration) << " of polling.";
    return stats;
  }

  return gutil::UnavailableErrorBuilder()
         << "stats unavailable after " << kPollDuration << " of polling";
}

absl::StatusOr<TrafficItemStats> GetTrafficItemStats(
    absl::string_view href, absl::string_view traffic_item_name,
    thinkit::GenericTestbed &generic_testbed) {
  ASSIGN_OR_RETURN(TrafficStats stats,
                   GetAllTrafficItemStats(href, generic_testbed));
  LOG(INFO) << "parsed traffic stats:\n" << stats.DebugString();
  return gutil::FindOrStatus(stats.stats_by_traffic_item(),
                             std::string(traffic_item_name));
}

absl::Status SetIpTrafficParameters(absl::string_view tref,
                                    const Ipv4TrafficParameters &params,
                                    thinkit::GenericTestbed &testbed) {
  RETURN_IF_ERROR(AppendIPv4(tref, testbed));
  RETURN_IF_ERROR(SetSrcIPv4(tref, params.src_ipv4.ToString(), testbed));
  RETURN_IF_ERROR(SetDestIPv4(tref, params.dst_ipv4.ToString(), testbed));
  if (params.priority.has_value()) {
    RETURN_IF_ERROR(SetIpPriority(tref, params.priority->dscp,
                                  params.priority->ecn, /*is_ipv4=*/true,
                                  testbed));
  }
  return absl::OkStatus();
}

absl::Status SetIpTrafficParameters(absl::string_view tref,
                                    const Ipv6TrafficParameters &params,
                                    thinkit::GenericTestbed &testbed) {
  RETURN_IF_ERROR(AppendIPv6(tref, testbed));
  RETURN_IF_ERROR(SetSrcIPv6(tref, params.src_ipv6.ToString(), testbed));
  RETURN_IF_ERROR(SetDestIPv6(tref, params.dst_ipv6.ToString(), testbed));
  if (params.priority.has_value()) {
    RETURN_IF_ERROR(SetIpPriority(tref, params.priority->dscp,
                                  params.priority->ecn, /*is_ipv4=*/false,
                                  testbed));
  }
  return absl::OkStatus();
}

absl::Status SetTrafficParameters(absl::string_view tref,
                                  const TrafficParameters &params,
                                  thinkit::GenericTestbed &testbed) {
  if (params.frame_count.has_value()) {
    RETURN_IF_ERROR(SetFrameCount(tref, *params.frame_count, testbed));
  }
  if (params.frame_size_in_bytes.has_value()) {
    RETURN_IF_ERROR(SetFrameSize(tref, *params.frame_size_in_bytes, testbed));
  }
  RETURN_IF_ERROR(std::visit(
      gutil::Overload{
          [&](FramesPerSecond speed) {
            return SetFrameRate(tref, speed.frames_per_second, testbed);
          },
          [&](PercentOfMaxLineRate speed) {
            return SetLineRate(tref, speed.percent_of_max_line_rate, testbed);
          }},
      params.traffic_speed));

  RETURN_IF_ERROR(SetSrcMac(tref, params.src_mac.ToString(), testbed));
  RETURN_IF_ERROR(SetDestMac(tref, params.dst_mac.ToString(), testbed));

  if (params.ip_parameters.has_value()) {
    RETURN_IF_ERROR(std::visit(
        [&](const auto &ip_params) {
          return SetIpTrafficParameters(tref, ip_params, testbed);
        },
        *params.ip_parameters));
  }

  return absl::OkStatus();
}

// Go over the connections and return vector of connections
// whose links are up.
absl::StatusOr<std::vector<IxiaLink>> GetReadyIxiaLinks(
    thinkit::GenericTestbed &generic_testbed,
    gnmi::gNMI::StubInterface &gnmi_stub) {
  std::vector<IxiaLink> links;

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed.GetSutInterfaceInfo();
  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  Add the pair to connections.
  for (const auto &[interface, info] : interface_info) {
    bool sut_link_up = false;
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      ASSIGN_OR_RETURN(sut_link_up, CheckLinkUp(interface, gnmi_stub));
      if (sut_link_up) {
        ASSIGN_OR_RETURN(int64_t bit_per_second,
                         GetPortSpeedInBitsPerSecond(interface, gnmi_stub));
        links.push_back(IxiaLink{
            .ixia_interface = info.peer_interface_name,
            .sut_interface = interface,
            .sut_interface_bits_per_second = bit_per_second,
        });
      }
    }
  }

  return links;
}

// Go over the connections and return Ixia link info.
absl::StatusOr<IxiaLink> GetIxiaLink(thinkit::GenericTestbed &generic_testbed,
                                     gnmi::gNMI::StubInterface &gnmi_stub,
                                     const std::string &switch_port) {
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed.GetSutInterfaceInfo();
  ASSIGN_OR_RETURN(thinkit::InterfaceInfo info,
                   gutil::FindOrStatus(interface_info, switch_port));
  ASSIGN_OR_RETURN(int64_t bits_per_second,
                   GetPortSpeedInBitsPerSecond(switch_port, gnmi_stub));
  return IxiaLink{.ixia_interface = info.peer_interface_name,
                  .sut_interface = switch_port,
                  .sut_interface_bits_per_second = bits_per_second};
}

// Connects to Ixia on the given testbed and returns a string handle identifying
// the connection (aka "topology ref").
absl::StatusOr<std::string> ConnectToIxia(thinkit::GenericTestbed &testbed) {
  ASSIGN_OR_RETURN(auto gnmi_stub, testbed.Sut().CreateGnmiStub());
  ASSIGN_OR_RETURN(std::vector<IxiaLink> ready_links,
                   GetReadyIxiaLinks(testbed, *gnmi_stub));
  if (ready_links.empty()) {
    return gutil::UnavailableErrorBuilder() << "no Ixia-to-SUT link up";
  }
  absl::string_view ixia_interface = ready_links[0].ixia_interface;
  ASSIGN_OR_RETURN(ixia::IxiaPortInfo ixia_port_info,
                   ixia::ExtractPortInfo(ixia_interface));
  ASSIGN_OR_RETURN(
      std::string ixia_connection_handle,
      pins_test::ixia::IxiaConnect(ixia_port_info.hostname, testbed));
  return ixia_connection_handle;
}

}  // namespace pins_test::ixia

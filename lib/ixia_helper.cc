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

#include <vector>

#include "absl/strings/escaping.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "include/nlohmann/json.hpp"

namespace pins_test::ixia {

using ::nlohmann::json;

// ExtractHref - Extract the href path from the Ixia response.
// An example response:
// {"links":[{"rel":"self","method":"GET","href":"/api/v1/sessions/82/ixnetwork/availableHardware/chassis/1"}]}
// which in this case would return
// href = /api/v1/sessions/82/ixnetwork/availableHardware/chassis/1
//
absl::StatusOr<std::string> ExtractHref(thinkit::HttpResponse &resp) {
  std::string href = "";
  json config_json = json::parse(resp.response);
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

  LOG(INFO) << "Received response " << chassis_response.response_code;
  LOG(INFO) << "Received response " << chassis_response.response;
  if (chassis_response.response_code != 201)
    return absl::InternalError(absl::StrFormat("unexpected response %d: %s",
                                               chassis_response.response_code,
                                               chassis_response.response));

  // Extract the href path from the response and return it.
  ASSIGN_OR_RETURN(std::string href, ExtractHref(chassis_response));
  return href;
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

  LOG(INFO) << "Received response " << connected_response.response_code;
  LOG(INFO) << "Received response " << connected_response.response;
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

  LOG(INFO) << "Received response " << traffic_response.response_code;
  LOG(INFO) << "Received response " << traffic_response.response;
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

  LOG(INFO) << "Received response " << endp_response.response_code;
  LOG(INFO) << "Received response " << endp_response.response;
  if (endp_response.response_code != 201)
    return absl::InternalError(absl::StrFormat("unexpected response %d: %s",
                                               endp_response.response_code,
                                               endp_response.response));

  return tref;
}

// SetupTrafficItem - Sets up a traffic item with source and destination port.
// Returns either an error or the
// href string for the first traffic item, e.g. something like
// "/api/v1/sessions/101/ixnetwork/traffic/trafficItem/1"
absl::StatusOr<std::string> SetUpTrafficItem(
    absl::string_view vref_src, absl::string_view vref_dst,
    thinkit::GenericTestbed &generic_testbed) {
  // POST to /traffic/trafficItem with:
  // [{"name":"Unicast Traffic"}]
  constexpr absl::string_view kTrafficPath = "/ixnetwork/traffic/trafficItem";
  constexpr absl::string_view kTrafficJson = "[{\"name\":\"Unicast Traffic\"}]";

  ASSIGN_OR_RETURN(
      thinkit::HttpResponse traffic_response,
      generic_testbed.SendRestRequestToIxia(thinkit::RequestType::kPost,
                                            kTrafficPath, kTrafficJson));

  LOG(INFO) << "Received response " << traffic_response.response_code;
  LOG(INFO) << "Received response " << traffic_response.response;
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

  LOG(INFO) << "Received response " << endp_response.response_code;
  LOG(INFO) << "Received response " << endp_response.response;
  if (endp_response.response_code != 201)
    return absl::InternalError(absl::StrFormat("unexpected response %d: %s",
                                               endp_response.response_code,
                                               endp_response.response));

  return tref;
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

  json resp_json = json::parse(response.response);
  json state_json = resp_json["state"];
  if (state_json.empty()) return absl::InternalError("no state");
  std::string state = state_json.get<std::string>();
  LOG(INFO) << "state = " << state;
  if (state == "SUCCESS") {
    LOG(INFO) << "state is success";
    return absl::OkStatus();
  }

  if (state != "IN_PROGRESS")
    return absl::InternalError(absl::StrFormat("unexpected state %s", state));

  json url_json = resp_json["url"];
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

    resp_json = json::parse(get_response.response);
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
  RETURN_IF_ERROR(WaitForComplete(generate_response, generic_testbed));

  // GET to /ixnetwork/traffic/trafficItem
  std::string titem_path = "/ixnetwork/traffic/trafficItem";
  LOG(INFO) << "path " << titem_path;
  ASSIGN_OR_RETURN(thinkit::HttpResponse titem_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kGet, titem_path, ""));
  LOG(INFO) << "Returns " << titem_response.response_code;
  LOG(INFO) << "Returns " << titem_response.response;
  // below code crashes for some reason... limit?  Response is like 1338ch.
  // json resp_json = json::parse(titem_response.response);
  // json state_json = resp_json["state"];
  // so coded doing string manipulation instead
  std::string temp = titem_response.response;
  std::size_t ixstate = temp.find("state");
  if (ixstate == std::string::npos) return absl::InternalError("no state");
  std::size_t ixquote = temp.find('"', ixstate + 8);
  if (ixquote == std::string::npos || ixquote <= ixstate + 8)
    return absl::InternalError("bad state");
  std::string state = temp.substr(ixstate + 8, ixquote - ixstate - 8);
  LOG(INFO) << "state is " << state;
  if (!(state == "started" || state == "startedWaitingForStats"))
    return absl::InternalError(absl::StrFormat("unexpected state: %s", state));
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

absl::Status SetFrameRate(absl::string_view tref, uint32_t fps,
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

absl::Status SetLineRate(absl::string_view tref, uint32_t percent,
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

absl::Status SetFrameCount(absl::string_view tref, uint32_t frames,
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

absl::Status SetFrameSize(absl::string_view tref, uint32_t framesize,
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
  LOG(INFO) << "Returns " << proto_response.response_code;
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
  LOG(INFO) << "Received response: " << append_response.response;
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
  LOG(INFO) << "Received response: " << append_response.response;
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

absl::Status SetIpPriority(absl::string_view tref, int dscp, bool is_ipv4,
                           int ecn_bits,
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
  std::string sip_json =
      absl::StrCat("{\"activeFieldChoice\":true,\"singleValue\":\"",
                   absl::StrFormat("%X", (dscp << 2) | (ecn_bits)), "\"}");
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
  LOG(INFO) << "Received response: " << append_response.response;
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
  LOG(INFO) << "Received response: " << append_response.response;
  return ixia::WaitForComplete(append_response, generic_testbed);
}

}  // namespace pins_test::ixia

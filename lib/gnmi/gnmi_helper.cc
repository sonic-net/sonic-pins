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

#include "lib/gnmi/gnmi_helper.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "google/protobuf/map.h"
#include "grpcpp/impl/codegen/client_context.h"
#include "grpcpp/impl/codegen/string_ref.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "re2/re2.h"
#include "include/nlohmann/json.hpp"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::nlohmann::json;
// Splits string in format "component[name=integrated_circuit0]" to three
// tokens.
const LazyRE2 kSplitNameValueRE = {R"((\w+)\[(\w+)=([\S+]+)\])"};

// Splits string to tokens seperated by a char '/' as long as '/' is not
// included in [].
const LazyRE2 kSplitBreakSquareBraceRE = {R"(([^\[\/]+(\[[^\]]+\])?)\/?)"};

}  // namespace

// This API generates gNMI path from OC path string.
// Example1:
// components/component[name=integrated_circuit0]/integrated-circuit/state.
// Example2:
// components/component[name=1/1]/integrated-circuit/state.
gnmi::Path ConvertOCStringToPath(absl::string_view oc_path) {
  absl::string_view element;
  std::vector<absl::string_view> elements;
  while (RE2::FindAndConsume(&oc_path, *kSplitBreakSquareBraceRE, &element)) {
    elements.push_back(element);
  }
  gnmi::Path path;
  for (absl::string_view node : elements) {
    std::string key;
    std::string attribute;
    std::string value;
    // "key/[attribute=value]" requests are in the format
    // Ex:interface[name=Ethernet0].
    if (RE2::FullMatch(node, *kSplitNameValueRE, &key, &attribute, &value)) {
      auto* elem = path.add_elem();
      elem->set_name(key);
      (*elem->mutable_key())[attribute] = value;
    } else {
      path.add_elem()->set_name(std::string(node));
    }
  }
  return path;
}

absl::StatusOr<gnmi::SetRequest> BuildGnmiSetRequest(
    absl::string_view oc_path, GnmiSetType set_type,
    absl::string_view json_val) {
  gnmi::SetRequest req;
  req.mutable_prefix()->set_origin(kOpenconfigStr);
  gnmi::Path* path;

  switch (set_type) {
    case GnmiSetType::kUpdate: {
      gnmi::Update* update = req.add_update();
      path = update->mutable_path();
      update->mutable_val()->set_json_ietf_val(std::string(json_val));
    } break;

    case GnmiSetType::kReplace: {
      gnmi::Update* replace = req.add_replace();
      path = replace->mutable_path();
      replace->mutable_val()->set_json_ietf_val(std::string(json_val));
    } break;

    case GnmiSetType::kDelete: {
      path = req.add_delete_();
    } break;

    default:
      return gutil::InternalErrorBuilder().LogError()
             << "Unknown gNMI Set Request";
  }

  *path = ConvertOCStringToPath(oc_path);
  return req;
}

absl::StatusOr<gnmi::GetRequest> BuildGnmiGetRequest(
    absl::string_view oc_path, gnmi::GetRequest::DataType req_type) {
  gnmi::GetRequest req;
  req.set_type(req_type);
  req.mutable_prefix()->set_origin(kOpenconfigStr);
  if (oc_path.empty()) {
    return req;
  }
  *req.add_path() = ConvertOCStringToPath(oc_path);
  return req;
}

absl::StatusOr<std::string> ParseGnmiGetResponse(
    const gnmi::GetResponse& response, absl::string_view match_tag) {
  if (response.notification_size() != 1)
    return gutil::InternalErrorBuilder().LogError()
           << "Unexpected size in response (should be 1): "
           << response.notification_size();

  if (response.notification(0).update_size() != 1)
    return gutil::InternalErrorBuilder().LogError()
           << "Unexpected update size in response (should be 1): "
           << response.notification(0).update_size();

  const auto resp_json =
      json::parse(response.notification(0).update(0).val().json_ietf_val());
  const auto match_tag_json = resp_json.find(match_tag);
  if (match_tag_json == resp_json.end()) {
    return gutil::InternalErrorBuilder().LogError()
           << match_tag << " not present in JSON response "
           << response.ShortDebugString();
  }
  return match_tag_json->dump();
}

absl::Status SetGnmiConfigPath(gnmi::gNMI::Stub* sut_gnmi_stub,
                               absl::string_view config_path,
                               GnmiSetType operation, absl::string_view value) {
  ASSIGN_OR_RETURN(gnmi::SetRequest request,
                   BuildGnmiSetRequest(config_path, operation, value));
  LOG(INFO) << "Sending SET request: " << request.ShortDebugString();
  gnmi::SetResponse response;
  grpc::ClientContext context;
  auto status = sut_gnmi_stub->Set(&context, request, &response);
  if (!status.ok()) {
    LOG(INFO) << "SET request failed! Error code: " << status.error_code()
              << " , Error message: " << status.error_message();
    return gutil::InternalErrorBuilder();
  }
  LOG(INFO) << "Received SET response: " << response.ShortDebugString();
  return absl::OkStatus();
}

absl::Status PushGnmiConfig(gnmi::gNMI::Stub& stub,
                            absl::string_view chassis_name,
                            const std::string& gnmi_config,
                            absl::uint128 election_id) {
  gnmi::SetRequest req;
  req.mutable_prefix()->set_origin("openconfig");
  req.mutable_prefix()->set_target(chassis_name);
  gnmi::Update* replace = req.add_replace();
  replace->mutable_path();
  replace->mutable_val()->set_json_ietf_val(gnmi_config);
  gnmi_ext::MasterArbitration* arbitration =
      req.add_extension()->mutable_master_arbitration();
  arbitration->mutable_role()->set_id("dataplane test");
  arbitration->mutable_election_id()->set_high(
      absl::Uint128High64(election_id));
  arbitration->mutable_election_id()->set_low(absl::Uint128Low64(election_id));

  gnmi::SetResponse resp;
  grpc::ClientContext context;
  grpc::Status status = stub.Set(&context, req, &resp);
  if (!status.ok()) return gutil::GrpcStatusToAbslStatus(status);
  LOG(INFO) << "Config push response: " << resp.ShortDebugString();
  return absl::OkStatus();
}

absl::Status PushGnmiConfig(thinkit::Switch& chassis,
                            const std::string& gnmi_config) {
  ASSIGN_OR_RETURN(std::unique_ptr<gnmi::gNMI::Stub> stub,
                   chassis.CreateGnmiStub());
  return pins_test::PushGnmiConfig(*stub, chassis.ChassisName(), gnmi_config);
}

absl::Status CanGetAllInterfaceOverGnmi(gnmi::gNMI::StubInterface& stub,
                                        absl::Duration timeout) {
  return GetAllInterfaceOverGnmi(stub).status();
}

absl::StatusOr<gnmi::GetResponse> GetAllInterfaceOverGnmi(
    gnmi::gNMI::StubInterface& stub, absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto req,
                   BuildGnmiGetRequest("interfaces", gnmi::GetRequest::STATE));
  gnmi::GetResponse resp;
  grpc::ClientContext context;
  context.set_wait_for_ready(true);
  context.set_deadline(absl::ToChronoTime(absl::Now() + timeout));
  grpc::Status status = stub.Get(&context, req, &resp);
  if (!status.ok()) return gutil::GrpcStatusToAbslStatus(status);
  LOG(INFO) << "Received GET response: " << resp.ShortDebugString();
  return resp;
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetInterfaceToOperStatusMapOverGnmi(gnmi::gNMI::StubInterface& stub,
                                    absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto req,
                   BuildGnmiGetRequest("interfaces", gnmi::GetRequest::STATE));
  gnmi::GetResponse resp;
  grpc::ClientContext context;
  context.set_deadline(absl::ToChronoTime(absl::Now() + timeout));
  grpc::Status status = stub.Get(&context, req, &resp);
  if (!status.ok()) return gutil::GrpcStatusToAbslStatus(status);
  if (resp.notification_size() < 1 || resp.notification(0).update_size() < 1) {
    return absl::InternalError(
        absl::StrCat("Invalid response: ", resp.DebugString()));
  }

  const auto resp_json = nlohmann::json::parse(
      resp.notification(0).update(0).val().json_ietf_val());
  const auto oc_intf_json = resp_json.find("openconfig-interfaces:interfaces");
  if (oc_intf_json == resp_json.end()) {
    return absl::NotFoundError(absl::StrCat(
        "'openconfig-interfaces:interfaces' not found: ", resp_json.dump()));
  }
  const auto oc_intf_list_json = oc_intf_json->find("interface");
  if (oc_intf_list_json == oc_intf_json->end()) {
    return absl::NotFoundError(
        absl::StrCat("'interface' not found: ", oc_intf_json->dump()));
  }

  absl::flat_hash_map<std::string, std::string> interface_to_oper_status_map;
  for (auto const& element : oc_intf_list_json->items()) {
    const auto element_name_json = element.value().find("name");
    if (element_name_json == element.value().end()) {
      return absl::NotFoundError(
          absl::StrCat("'name' not found: ", element.value().dump()));
    }
    std::string name = std::string(StripQuotes(element_name_json->dump()));

    // TODO: Remove once CpuX contains the oper-state subtree.
    if (absl::StartsWith(name, "Cpu")) {
      LOG(INFO) << "Skipping " << name << ".";
      continue;
    }

    const auto element_interface_state_json = element.value().find("state");
    if (element_interface_state_json == element.value().end()) {
      return absl::NotFoundError(absl::StrCat("'state' not found: ", name));
    }
    const auto element_status_json =
        element_interface_state_json->find("oper-status");
    if (element_status_json == element_interface_state_json->end()) {
      return absl::NotFoundError(
          absl::StrCat("'oper-status' not found: ", name));
    }
    interface_to_oper_status_map[name] =
        std::string(StripQuotes(element_status_json->dump()));
  }

  return interface_to_oper_status_map;
}

absl::Status CheckInterfaceOperStateOverGnmi(
    gnmi::gNMI::StubInterface& stub, absl::string_view interface_oper_state,
    absl::Span<const std::string> interfaces, absl::Duration timeout) {
  ASSIGN_OR_RETURN(const auto interface_to_oper_status_map,
                   GetInterfaceToOperStatusMapOverGnmi(stub, timeout));

  absl::flat_hash_set<std::string> matching_interfaces;
  for (const auto& [interface, oper_status] : interface_to_oper_status_map) {
    if (oper_status == interface_oper_state) {
      matching_interfaces.insert(interface);
    }
  }

  bool all_interfaces_found = true;
  for (const std::string& interface : interfaces) {
    if (!matching_interfaces.contains(interface)) {
      LOG(INFO) << "Interface "
                << interface << " not found in interfaces that are "
                << interface_oper_state;
      all_interfaces_found = false;
    }
  }

  if (!all_interfaces_found) {
    return absl::UnavailableError(
        absl::StrCat("Some interfaces are not in the expected "
                     "state.\nInterfaces provided: \n",
                     absl::StrJoin(interfaces, "\n"),
                     "\nInterfaces in the expected state: \n",
                     absl::StrJoin(matching_interfaces, "\n")));
  }
  return absl::OkStatus();
}

absl::Status CheckAllInterfaceOperStateOverGnmi(
    gnmi::gNMI::StubInterface& stub, absl::string_view interface_oper_state,
    bool skip_non_ethernet_interfaces, absl::Duration timeout) {
  ASSIGN_OR_RETURN(const auto interface_to_oper_status_map,
                   GetInterfaceToOperStatusMapOverGnmi(stub, timeout));

  std::vector<std::string> unavailable_interfaces;
  for (const auto& [interface, oper_status] : interface_to_oper_status_map) {
    if (skip_non_ethernet_interfaces &&
        !absl::StrContains(interface, "Ethernet")) {
      LOG(INFO) << "Skipping check on interface: " << interface;
      continue;
    }
    if (oper_status != interface_oper_state) {
      unavailable_interfaces.push_back(interface);
    }
  }
  if (!unavailable_interfaces.empty()) {
    return absl::UnavailableError(
        absl::StrCat("Interfaces are not ready. ",
                     absl::StrJoin(unavailable_interfaces, "\n")));
  }
  return absl::OkStatus();
}

absl::StatusOr<std::string> GetGnmiStatePathInfo(
    gnmi::gNMI::StubInterface* sut_gnmi_stub, absl::string_view state_path,
    absl::string_view resp_parse_str) {
  ASSIGN_OR_RETURN(gnmi::GetRequest request,
                   BuildGnmiGetRequest(state_path, gnmi::GetRequest::STATE));
  LOG(INFO) << "Sending GET request: " << request.ShortDebugString();
  gnmi::GetResponse response;
  grpc::ClientContext context;
  auto status = sut_gnmi_stub->Get(&context, request, &response);
  if (!status.ok()) {
    LOG(INFO) << "GET request failed! Error code: " << status.error_code()
              << " , Error message: " << status.error_message();
    return gutil::InternalErrorBuilder();
  }
  LOG(INFO) << "Received GET response: " << response.ShortDebugString();
  ASSIGN_OR_RETURN(std::string state_path_response,
                   ParseGnmiGetResponse(response, resp_parse_str));
  return state_path_response;
}

void AddSubtreeToGnmiSubscription(absl::string_view subtree_root,
                                  gnmi::SubscriptionList& subscription_list,
                                  gnmi::SubscriptionMode mode,
                                  bool suppress_redundant,
                                  absl::Duration interval) {
  gnmi::Subscription* subscription = subscription_list.add_subscription();
  subscription->set_mode(mode);
  if (mode == gnmi::SAMPLE) {
    subscription->set_sample_interval(absl::ToInt64Nanoseconds(interval));
  }
  subscription->set_suppress_redundant(suppress_redundant);
  *subscription->mutable_path() = ConvertOCStringToPath(subtree_root);
}

absl::StatusOr<std::vector<absl::string_view>>
GnmiGetElementFromTelemetryResponse(const gnmi::SubscribeResponse& response) {
  if (response.update().update_size() <= 0)
    return gutil::InternalErrorBuilder().LogError()
           << "Unexpected update size in response (should be > 0): "
           << response.update().update_size();
  LOG(INFO) << "Update size in response: " << response.update().update_size();

  std::vector<absl::string_view> elements;
  for (const auto& u : response.update().update()) {
    if (u.path().elem_size() <= 0)
      return gutil::InternalErrorBuilder().LogError()
             << "Unexpected element size in response (should be > 0): "
             << u.path().elem_size();

    for (const auto& e : u.path().elem()) {
      elements.push_back(e.name());
    }
  }
  return elements;
}

absl::StatusOr<std::vector<std::string>> GetUpInterfacesOverGnmi(
    gnmi::gNMI::StubInterface& stub, absl::Duration timeout) {
  ASSIGN_OR_RETURN(const auto interface_to_oper_status_map,
                   GetInterfaceToOperStatusMapOverGnmi(stub, timeout));

  std::vector<std::string> up_interfaces;
  for (const auto& [interface, oper_status] : interface_to_oper_status_map) {
    // Ignore the interfaces that is not EthernetXX. For example: bond0,
    // Loopback0, etc.
    if (!absl::StartsWith(interface, "Ethernet")) {
      LOG(INFO) << "Ignoring interface: " << interface;
      continue;
    }
    if (oper_status == "UP") {
      up_interfaces.push_back(interface);
    }
  }

  return up_interfaces;
}

absl::StatusOr<OperStatus> GetInterfaceOperStatusOverGnmi(
    gnmi::gNMI::StubInterface& stub, absl::string_view if_name) {
  std::string if_req = absl::StrCat("interfaces/interface[name=", if_name,
                                    "]/state/oper-status");
  ASSIGN_OR_RETURN(auto request,
                   BuildGnmiGetRequest(if_req, gnmi::GetRequest::STATE));

  gnmi::GetResponse response;
  grpc::ClientContext context;
  grpc::Status status = stub.Get(&context, request, &response);
  if (!status.ok()) return gutil::GrpcStatusToAbslStatus(status);

  if (response.notification_size() != 1 ||
      response.notification(0).update_size() != 1) {
    return absl::InternalError(
        absl::StrCat("Invalid response: ", response.DebugString()));
  }
  ASSIGN_OR_RETURN(
      std::string oper_status,
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"));

  if (absl::StrContains(oper_status, "UP")) {
    return OperStatus::kUp;
  }
  if (absl::StrContains(oper_status, "DOWN")) {
    return OperStatus::kDown;
  }
  if (absl::StrContains(oper_status, "TESTING")) {
    return OperStatus::kTesting;
  }
  return OperStatus::kUnknown;
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetAllInterfaceNameToPortId(gnmi::gNMI::StubInterface& stub) {
  ASSIGN_OR_RETURN(gnmi::GetResponse response,
                   pins_test::GetAllInterfaceOverGnmi(stub, absl::Seconds(60)));
  if (response.notification_size() < 1) {
    return absl::InternalError(
        absl::StrCat("Invalid response: ", response.DebugString()));
  }

  const auto response_json = nlohmann::json::parse(
      response.notification(0).update(0).val().json_ietf_val());
  const auto oc_intf_json =
      response_json.find("openconfig-interfaces:interfaces");
  if (oc_intf_json == response_json.end()) {
    return absl::NotFoundError(
        absl::StrCat("'openconfig-interfaces:interfaces' not found: ",
                     response_json.dump()));
  }
  const auto oc_intf_list_json = oc_intf_json->find("interface");
  if (oc_intf_list_json == oc_intf_json->end()) {
    return absl::NotFoundError(
        absl::StrCat("'interface' not found: ", oc_intf_json->dump()));
  }

  absl::flat_hash_map<std::string, std::string> interface_name_to_port_id;
  for (auto const& element : oc_intf_list_json->items()) {
    const auto element_name_json = element.value().find("name");
    if (element_name_json == element.value().end()) {
      return absl::NotFoundError(
          absl::StrCat("'name' not found: ", element.value().dump()));
    }
    std::string name = element_name_json->get<std::string>();

    // Ignore the interfaces that is not EthernetXX. For example: bond0,
    // Loopback0, etc.
    if (!absl::StartsWith(name, "Ethernet")) {
      LOG(INFO) << "Skipping " << name << ".";
      continue;
    }

    const auto element_interface_state_json = element.value().find("state");
    if (element_interface_state_json == element.value().end()) {
      return absl::NotFoundError(
          absl::StrCat("'state' not found: ", element.value().dump()));
    }

    const auto element_id_json =
        element_interface_state_json->find("openconfig-p4rt:id");
    if (element_id_json == element_interface_state_json->end()) {
      return absl::NotFoundError(absl::StrCat(
          "'openconfig-p4rt:id' not found: ", element.value().dump()));
    }
    interface_name_to_port_id[name] = absl::StrCat(element_id_json->get<int>());
  }
  return interface_name_to_port_id;
}

absl::StatusOr<std::vector<std::string>> ParseAlarms(
    const std::string& alarms_json) {
  auto alarms_array = json::parse(alarms_json);
  if (!alarms_array.is_array()) {
    return absl::InvalidArgumentError(
        "Input JSON should be an array of alarms.");
  }

  std::vector<std::string> alarm_messages;
  for (const auto& alarm : alarms_array) {
    auto state = alarm.find("state");
    if (state == alarm.end()) {
      return absl::InvalidArgumentError(
          "Input JSON alarm does not have a state field.");
    }

    // The state of an alarm will look like:
    // {
    //   "id": ...
    //   "resource": "linkqual:linkqual"
    //   "severity": "openconfig-alarm-types:WARNING"
    //   "text": "INACTIVE: Unknown"
    //   "time-created": ...
    //   "type-id": "Software Error"
    // }
    //
    // We can build an error message to look like (missing fields will be
    // omitted):
    // [linkqual:linkqual WARNING] Software Error INACTIVE: Unknown
    std::string message = "[";
    auto resource = state->find("resource");
    if (resource != state->end()) {
      absl::StrAppend(&message, StripQuotes(resource->dump()), " ");
    }
    auto severity = state->find("severity");
    if (severity != state->end()) {
      // We only need the last part.
      std::vector<std::string> parts =
          absl::StrSplit(StripQuotes(severity->dump()), ':');
      absl::StrAppend(&message, parts.back());
    }
    absl::StrAppend(&message, "] ");
    auto type_id = state->find("type-id");
    if (type_id != state->end()) {
      absl::StrAppend(&message, StripQuotes(type_id->dump()), " ");
    }
    auto text = state->find("text");
    if (text != state->end()) {
      absl::StrAppend(&message, StripQuotes(text->dump()));
    }
    alarm_messages.push_back(std::move(message));
  }
  return alarm_messages;
}

absl::StatusOr<std::vector<std::string>> GetAlarms(
    gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(
      gnmi::GetRequest request,
      BuildGnmiGetRequest("system/alarms", gnmi::GetRequest::STATE));
  LOG(INFO) << "Sending GET request: " << request.ShortDebugString();
  gnmi::GetResponse response;
  grpc::ClientContext context;
  grpc::Status status = gnmi_stub.Get(&context, request, &response);
  if (!status.ok()) {
    return gutil::GrpcStatusToAbslStatus(status);
  }

  LOG(INFO) << "Received GET response: " << response.ShortDebugString();
  if (response.notification_size() != 1) {
    return gutil::InternalErrorBuilder().LogError()
           << "Unexpected size in response (should be 1): "
           << response.notification_size();
  }
  if (response.notification(0).update_size() != 1) {
    return gutil::InternalErrorBuilder().LogError()
           << "Unexpected update size in response (should be 1): "
           << response.notification(0).update_size();
  }

  const auto response_json =
      json::parse(response.notification(0).update(0).val().json_ietf_val());
  const auto alarms_json = response_json.find("openconfig-system:alarms");
  // If alarms returns an empty subtree, assume no alarms and return an empty
  // list.
  if (alarms_json == response_json.end()) {
    return std::vector<std::string>();
  }

  const auto alarm_json = alarms_json->find("alarm");
  if (alarm_json == alarms_json->end()) {
    return std::vector<std::string>();
  }
  return ParseAlarms(alarm_json->dump());
}

absl::string_view StripQuotes(absl::string_view string) {
  return absl::StripPrefix(absl::StripSuffix(string, "\""), "\"");
}

}  // namespace pins_test

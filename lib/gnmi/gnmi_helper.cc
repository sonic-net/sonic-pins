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

#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_split.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.pb.h"
#include "re2/re2.h"
#include "include/nlohmann/json.hpp"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::nlohmann::json;
const LazyRE2 kSplitNameValueRE = {R"((\w+)\[(\w+)=([\w-]+)\])"};
}  // namespace

gnmi::Path ConvertOCStringToPath(absl::string_view oc_path) {
  gnmi::Path path;
  std::vector<absl::string_view> elements =
      absl::StrSplit(oc_path, absl::ByChar('/'), absl::SkipEmpty());
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
           << match_tag << "not present in JSON response "
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

absl::StatusOr<std::string> GetGnmiStatePathInfo(
    gnmi::gNMI::Stub* sut_gnmi_stub, absl::string_view state_path,
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
}  // namespace pins_test

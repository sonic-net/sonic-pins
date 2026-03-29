// Copyright 2026 Google LLC
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

// Minimal fake gNMI service modeling configurable Ethernet interfaces with P4RT
// port IDs. DVaaS uses gNMI to discover switch ports and check that they are
// up. This fake serves just enough to satisfy those queries.
//
// Runs as an in-process gRPC server. FourwardSwitch connects to its address.

#ifndef PINS_FOURWARD_FAKE_GNMI_SERVICE_H_
#define PINS_FOURWARD_FAKE_GNMI_SERVICE_H_

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "github.com/openconfig/gnmi/proto/gnmi/gnmi.grpc.pb.h"
#include "github.com/openconfig/gnmi/proto/gnmi/gnmi.pb.h"
#include "grpcpp/grpcpp.h"

namespace dvaas {

// A single modeled Ethernet interface.
struct FakeInterface {
  std::string name;
  int p4rt_id;
  bool enabled = true;
  std::string oper_status = "UP";
};

// Fake gNMI service that models a set of Ethernet interfaces.
// Interface state is immutable after construction.
class FakeGnmiService final : public gnmi::gNMI::Service {
 public:
  explicit FakeGnmiService(std::vector<FakeInterface> interfaces)
      : config_json_(BuildInterfacesJson(interfaces, /*config=*/true)),
        state_json_(BuildInterfacesJson(interfaces, /*config=*/false)) {}

  // Creates a default set of 8 Ethernet interfaces.
  static std::vector<FakeInterface> DefaultInterfaces() {
    std::vector<FakeInterface> result;
    for (int i = 0; i < 8; ++i) {
      result.push_back(
          {.name = absl::StrCat("Ethernet", i), .p4rt_id = i + 1});
    }
    return result;
  }

  grpc::Status Get(grpc::ServerContext* /*context*/,
                   const gnmi::GetRequest* request,
                   gnmi::GetResponse* response) override {
    gnmi::Notification* notification = response->add_notification();
    gnmi::Update* update = notification->add_update();
    update->mutable_val()->set_json_ietf_val(
        request->type() == gnmi::GetRequest::CONFIG ? config_json_
                                                    : state_json_);
    return grpc::Status::OK;
  }

  grpc::Status Set(grpc::ServerContext* /*context*/,
                   const gnmi::SetRequest* /*request*/,
                   gnmi::SetResponse* /*response*/) override {
    // Accept but ignore all Set requests. DVaaS uses Set to assign P4RT port
    // IDs, but our fake already has them pre-configured.
    return grpc::Status::OK;
  }

  grpc::Status Capabilities(
      grpc::ServerContext* /*context*/,
      const gnmi::CapabilityRequest* /*request*/,
      gnmi::CapabilityResponse* /*response*/) override {
    return grpc::Status(grpc::StatusCode::UNIMPLEMENTED,
                        "Capabilities not supported");
  }

  grpc::Status Subscribe(
      grpc::ServerContext* /*context*/,
      grpc::ServerReaderWriter<gnmi::SubscribeResponse,
                               gnmi::SubscribeRequest>* /*stream*/) override {
    return grpc::Status(grpc::StatusCode::UNIMPLEMENTED,
                        "Subscribe not supported");
  }

 private:
  static std::string BuildInterfacesJson(
      const std::vector<FakeInterface>& interfaces, bool config) {
    std::vector<std::string> entries;
    for (const FakeInterface& iface : interfaces) {
      std::string inner;
      if (config) {
        inner = absl::StrFormat(
            R"("config":{"name":"%s","type":"iana-if-type:ethernetCsmacd",)"
            R"("enabled":%s,"openconfig-p4rt:id":%d})",
            iface.name, iface.enabled ? "true" : "false", iface.p4rt_id);
      } else {
        inner = absl::StrFormat(
            R"("state":{"name":"%s","type":"iana-if-type:ethernetCsmacd",)"
            R"("enabled":%s,"oper-status":"%s","openconfig-p4rt:id":%d})",
            iface.name, iface.enabled ? "true" : "false", iface.oper_status,
            iface.p4rt_id);
      }
      entries.push_back(
          absl::StrFormat(R"({"name":"%s",%s})", iface.name, inner));
    }
    return absl::StrFormat(
        R"({"openconfig-interfaces:interfaces":{"interface":[%s]}})",
        absl::StrJoin(entries, ","));
  }

  const std::string config_json_;
  const std::string state_json_;
};

// Starts a FakeGnmiService on a random port. The server runs until the
// returned object is destroyed.
class FakeGnmiServer {
 public:
  // Starts a fake gNMI server with the given interfaces.
  static absl::StatusOr<std::unique_ptr<FakeGnmiServer>> Create(
      std::vector<FakeInterface> interfaces =
          FakeGnmiService::DefaultInterfaces()) {
    // Can't use make_unique due to private constructor.
    std::unique_ptr<FakeGnmiServer> result(
        new FakeGnmiServer(std::move(interfaces)));
    grpc::ServerBuilder builder;
    int port = 0;
    builder.AddListeningPort("localhost:0", grpc::InsecureServerCredentials(),
                             &port);
    builder.RegisterService(&result->service_);
    result->server_ = builder.BuildAndStart();
    if (result->server_ == nullptr) {
      return absl::InternalError("Failed to start fake gNMI server");
    }
    result->address_ = absl::StrCat("localhost:", port);
    return result;
  }

  const std::string& Address() const { return address_; }
  FakeGnmiService& Service() { return service_; }

 private:
  explicit FakeGnmiServer(std::vector<FakeInterface> interfaces)
      : service_(std::move(interfaces)) {}

  FakeGnmiService service_;
  std::unique_ptr<grpc::Server> server_;
  std::string address_;
};

}  // namespace dvaas

#endif  // PINS_FOURWARD_FAKE_GNMI_SERVICE_H_

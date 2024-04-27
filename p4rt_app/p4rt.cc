// Copyright 2022 Google LLC
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

#include <fstream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>  // NOLINT

#include "absl/flags/parse.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gflags/gflags.h"
#include "glog/logging.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/text_format.h"
#include "grpc/impl/codegen/grpc_types.h"
#include "grpcpp/security/authorization_policy_provider.h"
#include "grpcpp/security/server_credentials.h"
#include "grpcpp/security/tls_certificate_provider.h"
#include "grpcpp/security/tls_credentials_options.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"
#include "grpcpp/support/channel_arguments.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4rt_app/event_monitoring/app_state_db_port_table_event.h"
#include "p4rt_app/event_monitoring/config_db_node_cfg_table_event.h"
#include "p4rt_app/event_monitoring/config_db_port_table_event.h"
#include "p4rt_app/event_monitoring/state_event_monitor.h"
#include "p4rt_app/event_monitoring/state_verification_events.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/notification_producer_adapter.h"
#include "p4rt_app/sonic/adapters/producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/system_call_adapter.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "p4rt_app/sonic/packetio_impl.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "swss/dbconnector.h"
#include "swss/schema.h"

using ::grpc::Server;
using ::grpc::ServerBuilder;
using ::grpc::ServerCredentials;

#define APP_P4RT_CHANNEL_NAME                   "P4RT_CHANNEL"
// By default the P4RT App will run on TCP port 9559. Which is the IANA port
// reserved for P4Runtime.
// https://www.iana.org/assignments/service-names-port-numbers/service-names-port-numbers.xhtml?search=9559
DEFINE_int32(p4rt_grpc_port, 9559, "gRPC port for the P4Runtime Server");

// Optionally, the P4RT App can be run on a unix socket, but the connection will
// be insecure.
DEFINE_string(
    p4rt_unix_socket, "",
    "Unix socket file for internal insecure connections. Disabled if empty.");

// Runtime flags to configure any server credentials for secure conections.
DEFINE_bool(use_insecure_server_credentials, false, "Insecure gRPC.");
DEFINE_string(ca_certificate_file, "",
              "CA root certificate file, in PEM format. If set, p4rt will "
              "require and verify client certificate.");
DEFINE_string(server_certificate_file, "",
              "Server certificate file, in PEM format.");
DEFINE_string(server_key_file, "", "Server key file, in PEM format.");
DEFINE_bool(
    authz_policy_enabled, false,
    "Enable authz policy. Only take effect if use_insecure_server_credentials "
    "is false and mTLS is configured.");
DEFINE_string(authorization_policy_file, "/keys/authorization_policy.json",
              "File name of the JSON authorization policy file.");
DEFINE_string(cert_crl_dir, "", "Path to the CRL directory. Disable if empty");

// P4Runtime options:
DEFINE_bool(use_genetlink, false,
            "Enable Generic Netlink model for Packet Receive");
DEFINE_bool(use_port_ids, false,
            "Controller will use Port ID values configured over gNMI instead "
            "of the SONiC interface names.");
DEFINE_string(save_forwarding_config_file,
              "/etc/sonic/p4rt_forwarding_config.pb.txt",
              "Saves the forwarding pipeline config to a file so it can be "
              "reloaded after reboot.");

// We expect to run in the SONiC enviornment so the RedisDb connections are
// fixed, and connot be set by a flag.
constexpr char kRedisDbHost[] = "localhost";
constexpr int kRedisDbPort = 6379;

absl::StatusOr<std::shared_ptr<ServerCredentials>> BuildServerCredentials() {
  constexpr int kCertRefreshIntervalSec = 5;
  constexpr char kRootCertName[] = "root_cert";
  constexpr char kIdentityCertName[] = "switch_cert";

  std::shared_ptr<ServerCredentials> creds;
  if (FLAGS_use_insecure_server_credentials || FLAGS_server_key_file.empty() ||
      FLAGS_server_certificate_file.empty()) {
    creds = grpc::InsecureServerCredentials();
    if (creds == nullptr) {
      return gutil::InternalErrorBuilder()
             << "nullptr returned from grpc::InsecureServerCredentials";
    }
  } else {
    // If CA certificate is not provided, client certificate is not required.
    if (FLAGS_ca_certificate_file.empty()) {
      auto certificate_provider =
          std::make_shared<grpc::experimental::FileWatcherCertificateProvider>(
              FLAGS_server_key_file, FLAGS_server_certificate_file,
              kCertRefreshIntervalSec);
      grpc::experimental::TlsServerCredentialsOptions opts(
          certificate_provider);
      opts.watch_identity_key_cert_pairs();
      opts.set_identity_cert_name(kIdentityCertName);
      opts.set_cert_request_type(GRPC_SSL_DONT_REQUEST_CLIENT_CERTIFICATE);
      creds = grpc::experimental::TlsServerCredentials(opts);
    } else {
      auto certificate_provider =
          std::make_shared<grpc::experimental::FileWatcherCertificateProvider>(
              FLAGS_server_key_file, FLAGS_server_certificate_file,
              FLAGS_ca_certificate_file, kCertRefreshIntervalSec);
      grpc::experimental::TlsServerCredentialsOptions opts(
          certificate_provider);
      opts.watch_root_certs();
      opts.set_root_cert_name(kRootCertName);
      opts.watch_identity_key_cert_pairs();
      opts.set_identity_cert_name(kIdentityCertName);
      opts.set_cert_request_type(
          GRPC_SSL_REQUEST_AND_REQUIRE_CLIENT_CERTIFICATE_AND_VERIFY);

      // Set CRL Directory if it's not empty
      if (!FLAGS_cert_crl_dir.empty()) {
        opts.set_crl_directory(FLAGS_cert_crl_dir);
        LOG(INFO) << "CRL directory has been set";
      }
      creds = grpc::experimental::TlsServerCredentials(opts);
    }
    if (creds == nullptr) {
      return gutil::InternalErrorBuilder()
             << "nullptr returned from grpc::SslServerCredentials";
    }
  }
  return creds;
}

std::shared_ptr<grpc::experimental::AuthorizationPolicyProviderInterface>
CreateAuthzPolicyProvider() {
  constexpr int kAuthzRefreshIntervalSec = 5;
  grpc::Status status;
  auto provider =
      grpc::experimental::FileWatcherAuthorizationPolicyProvider::Create(
          FLAGS_authorization_policy_file, kAuthzRefreshIntervalSec, &status);
  if (!status.ok()) {
    LOG(ERROR) << "Failed to create authorization provider: "
               << gutil::GrpcStatusToAbslStatus(status);
    return nullptr;
  }
  return provider;
}

namespace p4rt_app {
namespace {

sonic::P4rtTable CreateP4rtTable(swss::DBConnector* app_db,
                                 swss::DBConnector* app_state_db,
                                 swss::DBConnector* counters_db) {
  const std::string kP4rtResponseChannel =
      std::string("APPL_DB_") + APP_P4RT_TABLE_NAME + "_RESPONSE_CHANNEL";

  return sonic::P4rtTable{
      .notification_producer =
          absl::make_unique<sonic::NotificationProducerAdapter>(
              app_db, APP_P4RT_CHANNEL_NAME),
      .notifier = absl::make_unique<sonic::ConsumerNotifierAdapter>(
          kP4rtResponseChannel, app_db),
      .app_state_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_state_db, APP_P4RT_TABLE_NAME),
      .counter_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          counters_db, COUNTERS_TABLE),
  };
}

void WaitForPortInitDone() {
  // Open a RedisDB connection to the AppDB.
  swss::DBConnector app_db(APPL_DB, kRedisDbHost, kRedisDbPort, /*timeout=*/0);

  // Wait for the ports to be initialized.
  while (!app_db.exists("PORT_TABLE:PortInitDone")) {
    // Prints once every 5 minutes.
    LOG_EVERY_N(WARNING, 60)
        << "Waiting for PortInitDone to be set before P4RT App will start.";
    absl::SleepFor(absl::Seconds(5));
  }
}

}  // namespace
}  // namespace p4rt_app

int main(int argc, char** argv) {
  google::InitGoogleLogging(argv[0]);
  gflags::ParseCommandLineFlags(&argc, &argv, true);

  // Open a database connection into the SONiC AppDb.
  swss::DBConnector app_db(APPL_DB, kRedisDbHost, kRedisDbPort, /*timeout=*/0);
  swss::DBConnector app_state_db(APPL_STATE_DB, kRedisDbHost, kRedisDbPort,
                                 /*timeout=*/0);
  swss::DBConnector counters_db(COUNTERS_DB, kRedisDbHost, kRedisDbPort,
                                /*timeout=*/0);

  // Create interfaces to interact with the P4RT_TABLE entries.
  p4rt_app::sonic::P4rtTable p4rt_table =
      p4rt_app::CreateP4rtTable(&app_db, &app_state_db, &counters_db);

  // Create PacketIoImpl for Packet I/O.
  auto packetio_impl = std::make_unique<p4rt_app::sonic::PacketIoImpl>(
      std::make_unique<p4rt_app::sonic::SystemCallAdapter>(),
      p4rt_app::sonic::PacketIoOptions{});

  // Wait for PortInitDone to be done.
  p4rt_app::WaitForPortInitDone();

  // Configure the P4RT options.
  p4rt_app::P4RuntimeImplOptions p4rt_options{
      .use_genetlink = FLAGS_use_genetlink,
      .translate_port_ids = FLAGS_use_port_ids,
  };

  std::string save_forwarding_config_file = FLAGS_save_forwarding_config_file;
  if (!save_forwarding_config_file.empty()) {
    p4rt_options.forwarding_config_full_path = save_forwarding_config_file;
  }

  // Create the P4RT server.
  p4rt_app::P4RuntimeImpl p4runtime_server(
      std::move(p4rt_table), std::move(packetio_impl), p4rt_options);

  // Create a server to listen on the unix socket port.
  std::thread internal_server_thread;
  if (!FLAGS_p4rt_unix_socket.empty()) {
    internal_server_thread = std::thread(
        [](p4rt_app::P4RuntimeImpl* p4rt_server) {
          ServerBuilder builder;
          builder.AddListeningPort(
              absl::StrCat("unix:", FLAGS_p4rt_unix_socket),
              grpc::InsecureServerCredentials());
          builder.RegisterService(p4rt_server);
          std::unique_ptr<Server> server(builder.BuildAndStart());
          LOG(INFO) << "Started unix socket server listening on "
                    << FLAGS_p4rt_unix_socket << ".";
          server->Wait();
        },
        &p4runtime_server);
  }

  // Spawn a separate thread that can react to AppStateDb changes.
  bool monitor_app_state_db_events = true;
  auto app_state_db_event_loop =
      std::thread([&p4runtime_server, &monitor_app_state_db_events]() {
        swss::DBConnector app_state_db("APPL_STATE_DB", /*timeout=*/0);
        p4rt_app::AppStateDbPortTableEventHandler port_table_handler(
            p4runtime_server);

        p4rt_app::sonic::StateEventMonitor port_state_monitor(app_state_db);
        auto status = port_state_monitor.RegisterTableHandler(
            "PORT_TABLE", port_table_handler);
        if (!status.ok()) {
          LOG(FATAL)  // Crash OK: only fails on startup.
              << "APPL_STATE_DB event monitor could not register 'PORT_TABLE': "
              << status;
        }

        while (monitor_app_state_db_events) {
          absl::Status status = port_state_monitor.WaitForNextEventAndHandle();
          if (!status.ok()) {
            LOG(ERROR)
                << "APPL_STATE_DB event monitor failed waiting for an event: "
                << status;
          }
        }
      });

  // Spawn a separate thread that can react to ConfigDb changes.
  bool monitor_config_db_events = true;
  auto config_db_event_loop = std::thread([&p4runtime_server,
                                           &monitor_config_db_events]() {
    swss::DBConnector config_db("CONFIG_DB", /*timeout=*/0);
    p4rt_app::sonic::StateEventMonitor config_db_monitor(config_db);

    p4rt_app::ConfigDbNodeCfgTableEventHandler node_table_handler(
        &p4runtime_server);
    auto node_table_status =
        config_db_monitor.RegisterTableHandler("NODE_CFG", node_table_handler);
    if (!node_table_status.ok()) {
      LOG(FATAL)  // Crash OK: only fails on startup.
          << "CONFIG_DB event monitor could not register 'NODE_CFG': "
          << node_table_status;
    }

    swss::DBConnector port_events_app_db("APPL_DB", /*timeout=*/0);
    swss::DBConnector port_events_app_state_db("APPL_STATE_DB", /*timeout=*/0);
    p4rt_app::ConfigDbPortTableEventHandler port_table_handler(
        &p4runtime_server,
        std::make_unique<p4rt_app::sonic::TableAdapter>(&port_events_app_db,
                                                        "P4RT_PORT_ID_TABLE"),
        std::make_unique<p4rt_app::sonic::TableAdapter>(
            &port_events_app_state_db, "P4RT_PORT_ID_TABLE"));
    auto port_table_status =
        config_db_monitor.RegisterTableHandler("PORT", port_table_handler);
    if (!port_table_status.ok()) {
      LOG(FATAL)  // Crash OK: only fails on startup.
          << "CONFIG_DB event monitor could not register 'PORT': "
          << port_table_status;
    }

    auto port_channel_table_status = config_db_monitor.RegisterTableHandler(
        "PORTCHANNEL", port_table_handler);
    if (!port_channel_table_status.ok()) {
      LOG(FATAL)  // Crash OK: only fails on startup.
          << "CONFIG_DB event monitor could not register 'PORTCHANNEL': "
          << port_channel_table_status;
    }

    while (monitor_config_db_events) {
      absl::Status status = config_db_monitor.WaitForNextEventAndHandle();
      if (!status.ok()) {
        LOG(ERROR) << "CONFIG_DB event monitor failed waiting for an event: "
                   << status;
      }
    }
  });

  // Start listening for state verification events, and update StateDb for P4RT.
  swss::DBConnector state_verification_db(STATE_DB, kRedisDbHost, kRedisDbPort,
                                          /*timeout=*/0);
  p4rt_app::sonic::TableAdapter state_verification_table_adapter(
      &state_verification_db, "VERIFY_STATE_RESP_TABLE");
  p4rt_app::sonic::ConsumerNotifierAdapter state_verification_notifier(
      "VERIFY_STATE_REQ_CHANNEL", &state_verification_db);
  p4rt_app::StateVerificationEvents state_verification_event_monitor(
      p4runtime_server, state_verification_notifier,
      state_verification_table_adapter);
  state_verification_event_monitor.Start();

  // Start a P4 runtime server
  ServerBuilder builder;
  auto server_cred = BuildServerCredentials();
  if (!server_cred.ok()) {
    LOG(ERROR) << "Failed to build server credentials, error "
               << server_cred.status();
    return -1;
  }

  std::string server_addr = absl::StrCat("[::]:", FLAGS_p4rt_grpc_port);
  builder.AddListeningPort(server_addr, *server_cred);

  // Set authorization policy.
  if (FLAGS_authz_policy_enabled && !FLAGS_ca_certificate_file.empty()) {
    auto provider = CreateAuthzPolicyProvider();
    if (provider == nullptr) {
      LOG(ERROR) << "Error in creating authz policy provider";
      return -1;
    }
    builder.experimental().SetAuthorizationPolicyProvider(std::move(provider));
  }

  builder.RegisterService(&p4runtime_server);

  std::unique_ptr<Server> server(builder.BuildAndStart());
  LOG(INFO) << "Server listening on " << server_addr << ".";
  server->Wait();

  LOG(INFO) << "Stopping the P4RT service.";
  monitor_app_state_db_events = false;
  monitor_config_db_events = false;
  app_state_db_event_loop.join();
  config_db_event_loop.join();

  return 0;
}

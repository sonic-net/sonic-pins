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

#include <chrono>  // NOLINT
#include <cstdint>
#include <fstream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>  // NOLINT
#include <utility>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/functional/bind_front.h"
#include "absl/log/initialize.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/synchronization/notification.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "grpc/grpc_crl_provider.h"
#include "grpcpp/security/audit_logging.h"
#include "grpcpp/security/authorization_policy_provider.h"
#include "grpcpp/security/server_credentials.h"
#include "grpcpp/security/tls_certificate_provider.h"
#include "grpcpp/security/tls_certificate_verifier.h"
#include "grpcpp/security/tls_credentials_options.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/syslog_sink.h"
#include "p4rt_app/event_monitoring/app_state_db_port_table_event.h"
#include "p4rt_app/event_monitoring/app_state_db_send_to_ingress_port_table_event.h"
#include "p4rt_app/event_monitoring/config_db_node_cfg_table_event.h"
#include "p4rt_app/event_monitoring/config_db_port_table_event.h"
#include "p4rt_app/event_monitoring/config_db_queue_table_event.h"
#include "p4rt_app/event_monitoring/debug_data_dump_events.h"
#include "p4rt_app/event_monitoring/state_event_monitor.h"
#include "p4rt_app/event_monitoring/state_verification_events.h"
#include "p4rt_app/event_monitoring/warm_boot_events.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/notification_producer_adapter.h"
#include "p4rt_app/sonic/adapters/producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/system_call_adapter.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "p4rt_app/sonic/adapters/warm_boot_state_adapter.h"
#include "p4rt_app/sonic/packetio_impl.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/utils/warm_restart_utility.h"
// TODO(PINS):
// #include "swss/component_state_helper.h"
// #include "swss/component_state_helper_interface.h"
#include "swss/dbconnector.h"
#include "swss/schema.h"

using ::grpc::Server;
using ::grpc::ServerBuilder;
using ::grpc::ServerCredentials;

#define APP_P4RT_VLAN_TABLE_NAME "VLAN_TABLE_P4"
#define APP_P4RT_VLAN_MEMBER_TABLE_NAME "VLAN_MEMBER_TABLE_P4"
#define APP_P4RT_CHANNEL_NAME "P4RT_TABLE"
// By default the P4RT App will run on TCP port 9559. Which is the IANA port
// reserved for P4Runtime.
// https://www.iana.org/assignments/service-names-port-numbers/service-names-port-numbers.xhtml?search=9559
ABSL_FLAG(int32_t, p4rt_grpc_port, 9559, "gRPC port for the P4Runtime Server");

// Optionally, the P4RT App can be run on a unix socket, but the connection will
// be insecure.
ABSL_FLAG(
    std::string, p4rt_unix_socket, "",
    "Unix socket file for internal insecure connections. Disabled if empty.");

// Runtime flags to configure any server credentials for secure conections.
ABSL_FLAG(bool, use_insecure_server_credentials, false, "Insecure gRPC.");
ABSL_FLAG(std::string, ca_certificate_file, "",
          "CA root certificate file, in PEM format. If set, p4rt will "
          "require and verify client certificate.");
ABSL_FLAG(std::string, server_certificate_file, "",
          "Server certificate file, in PEM format.");
ABSL_FLAG(std::string, server_key_file, "", "Server key file, in PEM format.");
ABSL_FLAG(
    bool, authz_policy_enabled, false,
    "Enable authz policy. Only take effect if use_insecure_server_credentials "
    "is false and mTLS is configured.");
ABSL_FLAG(std::string, authorization_policy_file,
          "/keys/authorization_policy.json",
          "File name of the JSON authorization policy file.");
ABSL_FLAG(std::string, cert_crl_dir, "",
          "Path to the CRL directory. CRL is disabled when empty.");

// P4Runtime options:
ABSL_FLAG(bool, use_genetlink, false,
          "Enable Generic Netlink model for Packet Receive");
ABSL_FLAG(bool, use_port_ids, false,
          "Controller will use Port ID values configured over gNMI instead "
          "of the SONiC interface names.");
ABSL_FLAG(std::string, save_forwarding_config_file,
          "/etc/sonic/p4rt_forwarding_config.pb.txt",
          "Saves the forwarding pipeline config to a file so it can be "
          "reloaded after reboot.");

absl::StatusOr<std::shared_ptr<ServerCredentials>> BuildServerCredentials() {
  constexpr int kCertRefreshIntervalSec = 5;
  constexpr int kCRLRefreshIntervalSec = 60;
  constexpr char kRootCertName[] = "root_cert";
  constexpr char kIdentityCertName[] = "switch_cert";

  std::shared_ptr<ServerCredentials> creds;
  if (absl::GetFlag(FLAGS_use_insecure_server_credentials) ||
      absl::GetFlag(FLAGS_server_key_file).empty() ||
      absl::GetFlag(FLAGS_server_certificate_file).empty()) {
    creds = grpc::InsecureServerCredentials();
    if (creds == nullptr) {
      return gutil::InternalErrorBuilder()
             << "nullptr returned from grpc::InsecureServerCredentials";
    }
  } else {
    // If CA certificate is not provided, client certificate is not required.
    if (absl::GetFlag(FLAGS_ca_certificate_file).empty()) {
      auto certificate_provider =
          std::make_shared<grpc::experimental::FileWatcherCertificateProvider>(
              absl::GetFlag(FLAGS_server_key_file),
              absl::GetFlag(FLAGS_server_certificate_file),
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
              absl::GetFlag(FLAGS_server_key_file),
              absl::GetFlag(FLAGS_server_certificate_file),
              absl::GetFlag(FLAGS_ca_certificate_file),
              kCertRefreshIntervalSec);
      grpc::experimental::TlsServerCredentialsOptions opts(
          certificate_provider);
      opts.watch_root_certs();
      opts.set_root_cert_name(kRootCertName);
      opts.watch_identity_key_cert_pairs();
      opts.set_identity_cert_name(kIdentityCertName);
      opts.set_cert_request_type(
          GRPC_SSL_REQUEST_AND_REQUIRE_CLIENT_CERTIFICATE_AND_VERIFY);

      // Set CRL Directory if it's not empty
      if (!absl::GetFlag(FLAGS_cert_crl_dir).empty()) {
        absl::StatusOr<std::shared_ptr<grpc_core::experimental::CrlProvider>>
            provider =
                grpc_core::experimental::CreateDirectoryReloaderCrlProvider(
                    absl::GetFlag(FLAGS_cert_crl_dir),
                    std::chrono::seconds(kCRLRefreshIntervalSec),
                    [](absl::Status status) {
                      LOG(ERROR) << "Failed to reload CRL: " << status;
                    });
        if (!provider.ok()) {
          return gutil::InternalErrorBuilder()
                 << "fail to create CRL provider: " << provider.status();
        }
        opts.set_crl_provider(*provider);
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
  grpc::Status status;
  auto provider =
      grpc::experimental::FileWatcherAuthorizationPolicyProvider::Create(
          absl::GetFlag(FLAGS_authorization_policy_file),
          /*refresh_interval_sec=*/5, &status);
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
                                 swss::DBConnector* counters_db) {
  const std::string kP4rtResponseChannel =
      std::string("APPL_DB_") + APP_P4RT_TABLE_NAME + "_RESPONSE_CHANNEL";

  return sonic::P4rtTable{
      .notification_producer =
          absl::make_unique<sonic::NotificationProducerAdapter>(
              app_db, APP_P4RT_CHANNEL_NAME),
      .notification_consumer =
          absl::make_unique<sonic::ConsumerNotifierAdapter>(
              kP4rtResponseChannel, app_db),
      .app_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_db, APP_P4RT_TABLE_NAME),
      .counter_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          counters_db, COUNTERS_TABLE),
  };
}

sonic::VrfTable CreateVrfTable(swss::DBConnector* app_db,
                               swss::DBConnector* app_state_db) {
  const std::string kVrfResponseChannel = "APPL_DB_VRF_TABLE_RESPONSE_CHANNEL";

  return sonic::VrfTable{
      .producer_state = absl::make_unique<sonic::ProducerStateTableAdapter>(
          app_db, APP_VRF_TABLE_NAME),
      .notification_consumer =
          absl::make_unique<sonic::ConsumerNotifierAdapter>(
              kVrfResponseChannel, app_db),
      .app_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_db, APP_VRF_TABLE_NAME),
      .app_state_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_state_db, APP_VRF_TABLE_NAME),
  };
}

sonic::VlanTable CreateVlanTable(swss::DBConnector* app_db,
                                 swss::DBConnector* app_state_db) {
  const std::string kVlanResponseChannel =
      absl::StrCat("APPL_DB_", APP_P4RT_VLAN_TABLE_NAME, "_RESPONSE_CHANNEL");
  const std::string kVlanMemberResponseChannel = absl::StrCat(
      "APPL_DB_", APP_P4RT_VLAN_MEMBER_TABLE_NAME, "_RESPONSE_CHANNEL");

  return sonic::VlanTable{
      .producer_state = absl::make_unique<sonic::ProducerStateTableAdapter>(
          app_db, APP_P4RT_VLAN_TABLE_NAME),
      .notification_consumer =
          absl::make_unique<sonic::ConsumerNotifierAdapter>(
              kVlanResponseChannel, app_db),
      .app_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_db, APP_P4RT_VLAN_TABLE_NAME),
      .app_state_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_state_db, APP_P4RT_VLAN_TABLE_NAME),
  };
}

sonic::VlanMemberTable CreateVlanMemberTable(swss::DBConnector* app_db,
                                             swss::DBConnector* app_state_db) {
  const std::string kVlanMemberResponseChannel = absl::StrCat(
      "APPL_DB_", APP_P4RT_VLAN_MEMBER_TABLE_NAME, "_RESPONSE_CHANNEL");

  return sonic::VlanMemberTable{
      .producer_state = absl::make_unique<sonic::ProducerStateTableAdapter>(
          app_db, APP_P4RT_VLAN_MEMBER_TABLE_NAME),
      .notification_consumer =
          absl::make_unique<sonic::ConsumerNotifierAdapter>(
              kVlanMemberResponseChannel, app_db),
      .app_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_db, APP_P4RT_VLAN_MEMBER_TABLE_NAME),
      .app_state_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_state_db, APP_P4RT_VLAN_MEMBER_TABLE_NAME),
  };
}

sonic::HashTable CreateHashTable(swss::DBConnector* app_db,
                                 swss::DBConnector* app_state_db) {
  const std::string kAppHashTableName = "HASH_TABLE";
  const std::string kHashResponseChannel =
      "APPL_DB_HASH_TABLE_RESPONSE_CHANNEL";

  return sonic::HashTable{
      .producer_state = absl::make_unique<sonic::ProducerStateTableAdapter>(
          app_db, kAppHashTableName),
      .notification_consumer =
          absl::make_unique<sonic::ConsumerNotifierAdapter>(
              kHashResponseChannel, app_db),
      .app_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_db, kAppHashTableName),
      .app_state_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_state_db, kAppHashTableName),
  };
}

sonic::SwitchTable CreateSwitchTable(swss::DBConnector* app_db,
                                     swss::DBConnector* app_state_db) {
  const std::string kAppSwitchTableName = "SWITCH_TABLE";
  const std::string kSwitchResponseChannel =
      "APPL_DB_SWITCH_TABLE_RESPONSE_CHANNEL";

  return sonic::SwitchTable{
      .producer_state = absl::make_unique<sonic::ProducerStateTableAdapter>(
          app_db, kAppSwitchTableName),
      .notification_consumer =
          absl::make_unique<sonic::ConsumerNotifierAdapter>(
              kSwitchResponseChannel, app_db),
      .app_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_db, kAppSwitchTableName),
      .app_state_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_state_db, kAppSwitchTableName),
  };
}

sonic::PortTable CreatePortTable(swss::DBConnector* app_db,
                                 swss::DBConnector* app_state_db) {
  const std::string kPortTableName = "P4RT_PORT_ID_TABLE";
  return sonic::PortTable{
      .app_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_db, kPortTableName),
      .app_state_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          app_state_db, kPortTableName),
  };
}

sonic::HostStatsTable CreateHostStatsTable(swss::DBConnector* state_db) {
  return sonic::HostStatsTable{
      .state_db = absl::make_unique<p4rt_app::sonic::TableAdapter>(
          state_db, "HOST_STATS")};
}

void LogStatsEveryMinute(absl::Notification* stop,
                         p4rt_app::P4RuntimeImpl* p4runtime) {
  while (!stop->HasBeenNotified()) {
    absl::SleepFor(absl::Minutes(1));

    auto stats = p4runtime->GetFlowProgrammingStatistics();
    if (!stats.ok()) {
      LOG(ERROR) << "Failed to get P4Runtime statistics: " << stats.status();
      continue;
    }

    // Reads and writes happen independently, but the controller will read every
    // few seconds to verify correctness. To avoid being spammy we will only log
    // performance when changes are made to the switch (i.e. when we see a
    // write).
    if (stats->write_batch_count > 0) {
      LOG(INFO) << absl::StreamFormat(
          "Spent %d microseconds handling %d write requests from %d batches "
          "over the past minute with the longest batch taking %dus.",
          absl::ToInt64Microseconds(stats->write_time),
          stats->write_requests_count, stats->write_batch_count,
          absl::ToInt64Microseconds(stats->max_write_time));

      if (stats->read_request_count > 0) {
        LOG(INFO) << absl::StreamFormat(
            "Spent %d microseconds handling %d read requests over the past "
            "minute.",
            absl::ToInt64Microseconds(stats->read_time),
            stats->read_request_count);
      }
    }
  }
}

// Construct and register a table handler with the given state monitor.
template <typename T, typename... Args>
void RegisterTableHandlerOrDie(p4rt_app::sonic::StateEventMonitor& monitor,
                               absl::string_view table_name, Args... args) {
  absl::Status result =
      monitor.RegisterTableHandler(table_name, std::make_unique<T>(args...));
  if (!result.ok()) LOG(FATAL) << result;  // Crash OK: only fails on startup.
}

void AppStateDbEventLoop(P4RuntimeImpl* p4runtime_server,
                         bool* monitor_app_state_db_events) {
  swss::DBConnector app_state_db("APPL_STATE_DB", /*timeout=*/0);
  p4rt_app::sonic::StateEventMonitor app_state_db_monitor(app_state_db);

  RegisterTableHandlerOrDie<p4rt_app::AppStateDbPortTableEventHandler>(
      app_state_db_monitor, "PORT_TABLE", p4runtime_server);
  RegisterTableHandlerOrDie<
      p4rt_app::AppStateDbSendToIngressPortTableEventHandler>(
      app_state_db_monitor, APP_SEND_TO_INGRESS_PORT_TABLE_NAME,
      p4runtime_server);

  while (*monitor_app_state_db_events) {
    absl::Status status = app_state_db_monitor.WaitForNextEventAndHandle();
    if (!status.ok()) {
      LOG(ERROR) << "APPL_STATE_DB event monitor failed waiting for an event: "
                 << status;
    }
  }
}

void ConfigDbEventLoop(P4RuntimeImpl* p4runtime_server,
                       bool* monitor_config_db_events) {
  swss::DBConnector config_db("CONFIG_DB", /*timeout=*/0);
  p4rt_app::sonic::StateEventMonitor config_db_monitor(config_db);

  RegisterTableHandlerOrDie<p4rt_app::ConfigDbNodeCfgTableEventHandler>(
      config_db_monitor, "NODE_CFG", p4runtime_server);
  RegisterTableHandlerOrDie<p4rt_app::ConfigDbPortTableEventHandler>(
      config_db_monitor, "PORT", p4runtime_server);
  RegisterTableHandlerOrDie<p4rt_app::ConfigDbPortTableEventHandler>(
      config_db_monitor, "PORTCHANNEL", p4runtime_server);
  RegisterTableHandlerOrDie<p4rt_app::ConfigDbPortTableEventHandler>(
      config_db_monitor, "CPU_PORT", p4runtime_server);
  RegisterTableHandlerOrDie<p4rt_app::ConfigDbQueueTableEventHandler>(
      config_db_monitor, "QUEUE_NAME_TO_ID_MAP", p4runtime_server);

  while (*monitor_config_db_events) {
    absl::Status status = config_db_monitor.WaitForNextEventAndHandle();
    if (!status.ok()) {
      LOG(ERROR) << "CONFIG_DB event monitor failed waiting for an event: "
                 << status;
    }
  }
}

// Create a WarmRestartUtil object and initialize it.
p4rt_app::WarmRestartUtil MakeWarmRestartUtil(swss::DBConnector& config_db) {
  return p4rt_app::WarmRestartUtil(
      std::make_unique<p4rt_app::sonic::WarmBootStateAdapter>(),
      std::make_shared<p4rt_app::sonic::TableAdapter>(&config_db, "PORT"),
      std::make_shared<p4rt_app::sonic::TableAdapter>(&config_db, "CPU_PORT"),
      std::make_shared<p4rt_app::sonic::TableAdapter>(&config_db,
                                                      "PORTCHANNEL"),
      std::make_unique<p4rt_app::sonic::TableAdapter>(&config_db,
                                                      "QUEUE_NAME_TO_ID_MAP"),
      std::make_unique<p4rt_app::sonic::TableAdapter>(&config_db, "NODE_CFG"),
      std::make_unique<p4rt_app::sonic::TableAdapter>(&config_db,
                                                      "SEND_TO_INGRESS_PORT"));
}

}  // namespace
}  // namespace p4rt_app

int main(int argc, char** argv) {
  gutil::SyslogSink syslog_sink("p4rt");
  
  absl::InitializeLog();
  absl::ParseCommandLine(argc, argv);

  /*TODO(PINS): Get the P4RT component helper which can be used to put the switch into
  // critical state.
  swss::ComponentStateHelperInterface& component_state_singleton =
      swss::StateHelperManager::ComponentSingleton(
          swss::SystemComponent::kP4rt);

  //TODO(PINS): Get the system state helper which will be used to verify the switch is
  // healthy, and not in a critical state before handling P4 Runtime requests.
  swss::SystemStateHelperInterface& system_state_singleton =
      swss::StateHelperManager::SystemSingleton();
*/

  // Open a database connection into the SONiC AppDb.
  swss::DBConnector app_db("APPL_DB", /*timeout=*/0);
  swss::DBConnector app_state_db("APPL_STATE_DB", /*timeout=*/0);
  swss::DBConnector counters_db("COUNTERS_DB", /*timeout=*/0);
  swss::DBConnector state_db("STATE_DB", /*timeout=*/0);
  swss::DBConnector config_db("CONFIG_DB", /*timeout=*/0);

  // Create interfaces to interact with the P4RT_TABLE entries.
  p4rt_app::sonic::P4rtTable p4rt_table =
      p4rt_app::CreateP4rtTable(&app_db, &counters_db);
  p4rt_app::sonic::VrfTable vrf_table =
      p4rt_app::CreateVrfTable(&app_db, &app_state_db);
  p4rt_app::sonic::VlanTable vlan_table =
      p4rt_app::CreateVlanTable(&app_db, &app_state_db);
  p4rt_app::sonic::VlanMemberTable vlan_member_table =
      p4rt_app::CreateVlanMemberTable(&app_db, &app_state_db);
  p4rt_app::sonic::HashTable hash_table =
      p4rt_app::CreateHashTable(&app_db, &app_state_db);
  p4rt_app::sonic::SwitchTable switch_table =
      p4rt_app::CreateSwitchTable(&app_db, &app_state_db);
  p4rt_app::sonic::PortTable port_table =
      p4rt_app::CreatePortTable(&app_db, &app_state_db);
  p4rt_app::sonic::HostStatsTable host_stats_table =
      p4rt_app::CreateHostStatsTable(&state_db);

  // Create PacketIoImpl for Packet I/O.
  auto packetio_impl = std::make_unique<p4rt_app::sonic::PacketIoImpl>(
      std::make_unique<p4rt_app::sonic::SystemCallAdapter>(),
      // std::make_unique<swss::IntfTranslator>(&config_db),
      p4rt_app::sonic::PacketIoOptions{});

  // TODO(PINS): Create a netdev translator for P4Runtime's PacketIo handling.
  //  swss::IntfTranslator netdev_translator(&config_db);

  // Configure the P4RT options.
  p4rt_app::P4RuntimeImplOptions p4rt_options{
      .use_genetlink = absl::GetFlag(FLAGS_use_genetlink),
      .translate_port_ids = absl::GetFlag(FLAGS_use_port_ids),
  };

  std::string save_forwarding_config_file =
      absl::GetFlag(FLAGS_save_forwarding_config_file);
  if (!save_forwarding_config_file.empty()) {
    p4rt_options.forwarding_config_full_path = save_forwarding_config_file;
  }

  p4rt_app::WarmRestartUtil warm_restart_util =
      p4rt_app::MakeWarmRestartUtil(config_db);

  bool is_warm_start = warm_restart_util.IsWarmStart();
  p4rt_options.is_freeze_mode = is_warm_start;

  // Create the P4RT server. If boot up in warm start mode, set p4runtime_server
  // in freeze mode to reject requests until unfreeze.
  p4rt_app::P4RuntimeImpl p4runtime_server(
      std::move(p4rt_table), std::move(vrf_table), std::move(vlan_table),
      std::move(vlan_member_table), std::move(hash_table),
      std::move(switch_table), std::move(port_table), std::move(host_stats_table), 
      std::make_unique<p4rt_app::sonic::WarmBootStateAdapter>(),
      std::move(packetio_impl),
      //TODO(PINS): To add component_state_singleton, system_state_singleton, netdev_translator
      //component_state_singleton, system_state_singleton, netdev_translator,
      p4rt_options);

  if (is_warm_start) {
    // Set warm-start state to INITIALIZED if boot up in warm-start mode.
    p4runtime_server.GrabLockAndUpdateWarmBootState(
        swss::WarmStart::WarmStartState::INITIALIZED);
    auto reconciliation_status = p4runtime_server.RebuildSwStateAfterWarmboot(
        warm_restart_util.GetPortIdsFromConfigDb(),
        warm_restart_util.GetCpuQueueIdsFromConfigDb(),
        warm_restart_util.GetFrontPanelQueueIdsFromConfigDb(),
        warm_restart_util.GetDeviceIdFromConfigDb(),
        warm_restart_util.GetPortsFromConfigDb());
    if (reconciliation_status.ok()) {
      swss::WarmStart::setWarmStartState(
          "p4rt", swss::WarmStart::WarmStartState::RECONCILED);
    }
  }

  // Create a server to listen on the unix socket port.
  std::thread internal_server_thread;
  std::string unix_socket = absl::GetFlag(FLAGS_p4rt_unix_socket);
  if (!unix_socket.empty()) {
    internal_server_thread = std::thread(
        [unix_socket](p4rt_app::P4RuntimeImpl* p4rt_server) {
          ServerBuilder builder;
          builder.AddListeningPort(absl::StrCat("unix:", unix_socket),
                                   grpc::InsecureServerCredentials());
          builder.RegisterService(p4rt_server);
          std::unique_ptr<Server> server(builder.BuildAndStart());
          LOG(INFO) << "Started unix socket server listening on " << unix_socket
                    << ".";
          server->Wait();
        },
        &p4runtime_server);
  }

  // Spawn a separate thread that can react to AppStateDb changes.
  bool monitor_app_state_db_events = true;
  auto app_state_db_event_loop = std::thread(
      absl::bind_front(&p4rt_app::AppStateDbEventLoop, &p4runtime_server,
                       &monitor_app_state_db_events));

  // Spawn a separate thread that can react to ConfigDb changes.
  bool monitor_config_db_events = true;
  auto config_db_event_loop = std::thread(
      absl::bind_front(&p4rt_app::ConfigDbEventLoop, &p4runtime_server,
                       &monitor_config_db_events));

  // Start listening for state verification events, and update StateDb for P4RT.
  swss::DBConnector state_verification_db("STATE_DB", /*timeout=*/0);
  p4rt_app::sonic::TableAdapter state_verification_table_adapter(
      &state_verification_db, "VERIFY_STATE_RESP_TABLE");
  p4rt_app::sonic::ConsumerNotifierAdapter state_verification_notifier(
      "VERIFY_STATE_REQ_CHANNEL", &state_verification_db);
  p4rt_app::StateVerificationEvents state_verification_event_monitor(
      p4runtime_server, state_verification_notifier,
      state_verification_table_adapter);
  state_verification_event_monitor.Start();

  // Start listening for debug data dump events.
  p4rt_app::sonic::ConsumerNotifierAdapter debug_data_dump_notifier(
      "DEBUG_DATA_REQ_CHANNEL", &app_db);
  p4rt_app::sonic::NotificationProducerAdapter debug_data_dump_responder(
      &app_db, "DEBUG_DATA_RESP_CHANNEL");
  p4rt_app::DebugDataDumpEventHandler debug_data_dump_event_monitor(
      p4runtime_server, debug_data_dump_notifier, debug_data_dump_responder);
  debug_data_dump_event_monitor.Start();

  // Report performance statistics every minute.
  absl::Notification stop_stats_logging;
  std::thread stats_logging_loop(p4rt_app::LogStatsEveryMinute,
                                 &stop_stats_logging, &p4runtime_server);

  // Start a P4 runtime server
  ServerBuilder builder;
  auto server_cred = BuildServerCredentials();
  if (!server_cred.ok()) {
    LOG(ERROR) << "Failed to build server credentials, error "
               << server_cred.status();
    return -1;
  }

  std::string server_addr =
      absl::StrCat("[::]:", absl::GetFlag(FLAGS_p4rt_grpc_port));
  builder.AddListeningPort(server_addr, *server_cred);

  // Set authorization policy.
  if (absl::GetFlag(FLAGS_authz_policy_enabled) &&
      !absl::GetFlag(FLAGS_ca_certificate_file).empty()) {
    auto provider = CreateAuthzPolicyProvider();
    if (provider == nullptr) {
      LOG(ERROR) << "Error in creating authz policy provider";
      return -1;
    }
    builder.experimental().SetAuthorizationPolicyProvider(std::move(provider));
  }

  builder.RegisterService(&p4runtime_server);

  // Disable max ping strikes behavior to allow more frequent KA.
  builder.AddChannelArgument(GRPC_ARG_HTTP2_MAX_PING_STRIKES, 0);

  // Sends KeepAlive pings to client to ensure P4RT can promptly discover
  // disconnects and vacate the role of primary controller. Else, backup
  // connection might not be able to connect to P4RT with the same election id.
  builder.AddChannelArgument(GRPC_ARG_KEEPALIVE_TIME_MS, 1000);

  // Keepalive pings' timeout.
  // Despite the switch wanting to discover disconnects as soon as possible the
  // keepalive timeout can not be too fast. Else there won't be enough time for
  // the switch's teaming driver to failover. We settle with 20s since this is
  // the timeout value a P4 client would usually have.
  builder.AddChannelArgument(GRPC_ARG_KEEPALIVE_TIMEOUT_MS, 20'000);

  // Sends KA pings even when existing streaming RPC is not active.
  builder.AddChannelArgument(GRPC_ARG_HTTP2_MAX_PINGS_WITHOUT_DATA, 0);

  std::unique_ptr<Server> server(builder.BuildAndStart());
  LOG(INFO) << "Server listening on " << server_addr << ".";
  server->Wait();

  LOG(INFO) << "Stopping the P4RT service.";
  monitor_app_state_db_events = false;
  monitor_config_db_events = false;
  stop_stats_logging.Notify();
  app_state_db_event_loop.join();
  config_db_event_loop.join();
  stats_logging_loop.join();

  return 0;
}

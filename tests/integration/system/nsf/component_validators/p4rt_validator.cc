// Copyright 2025 Google LLC
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
#include "tests/integration/system/nsf/component_validators/p4rt_validator.h"

#include <string>

#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/ascii.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "gutil/gutil/status.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/ssh_client.h"

namespace pins_test {
namespace {

constexpr char kSyslogFile[] = "/var/log/tmp/sandcastle.log";
constexpr char kGrepAclRecarvedTablesCmd[] =
    "grep \'Removing modified nonessential ACL table\' $0 | cut -d ' ' -f 16";
constexpr absl::Duration kRunCommandTimeout = absl::Minutes(1);

absl::Status VerifyAclRecarvingTelemetry(absl::string_view version,
                                         const Testbed& testbed,
                                         thinkit::SSHClient& ssh_client) {
  ASSIGN_OR_RETURN(auto sut_gnmi_stub, GetSut(testbed).CreateGnmiStub());
  ASSIGN_OR_RETURN(PinsSoftwareComponentInfo software_info,
                   GetPinsSoftwareComponentInfo(*sut_gnmi_stub));

  if (software_info.primary_network_stack.version ==
      software_info.secondary_network_stack.version) {
    // There shouldn't be any ACL recarving when a config is pushed between same
    // versions of NSF upgrade.
    return absl::OkStatus();
  }

  // Add release specific objects in the allow list.
  absl::flat_hash_set<absl::string_view> allowlist;
  
  std::string allowlist_str;
  for (const auto obj : allowlist) {
    absl::StrAppend(&allowlist_str, obj, ", ");
  }
  if (!allowlist.empty()) {
    LOG(INFO) << absl::Substitute("ACL recarving allow list for $0 -> $1: $2",
                                  software_info.secondary_network_stack.version,
                                  software_info.primary_network_stack.version,
                                  allowlist_str);
  }

  // TODO: Replace fetching recarved ACL tables from syslog via SSH
  // with blackbox interfaces.
  // Fetch recarved ACL tables from syslog.
  ASSIGN_OR_RETURN(auto recarved_acl_tables,
                   ssh_client.RunCommand(
                       GetSut(testbed).ChassisName(),
                       absl::Substitute(kGrepAclRecarvedTablesCmd, kSyslogFile),
                       kRunCommandTimeout));
  absl::StripAsciiWhitespace(&recarved_acl_tables);
  if (recarved_acl_tables.empty()) {
    // No ACL recarving occurred during config push.
    return absl::OkStatus();
  }
  LOG(INFO) << "Recarved ACL tables: " << recarved_acl_tables;

  std::string error_msg;
  for (absl::string_view acl_table :
       absl::StrSplit(recarved_acl_tables, '\n')) {
    // ACL tables returned from syslog are enclosed within single quotes. For
    // example: 'acl_ingress_table', 'acl_ingress_qos_table' etc.
    absl::ConsumePrefix(&acl_table, "'");
    absl::ConsumeSuffix(&acl_table, "'");
    if (acl_table.empty()) {
      continue;
    }
    if (!allowlist.contains(acl_table)) {
      absl::StrAppend(
          &error_msg,
          absl::Substitute(
              "Recarved ACL table $0 is not in the allow list: $1\n", acl_table,
              allowlist_str));
    }
  }
  if (!error_msg.empty()) {
    LOG(ERROR) << "ACL recarving validation failed: " << error_msg;
    return absl::InternalError(error_msg);
  }
  return absl::OkStatus();
}

}  // namespace

absl::Status P4rtValidator::OnConfigPush(absl::string_view version,
                                         const Testbed& testbed,
                                         thinkit::SSHClient& ssh_client) {
  return VerifyAclRecarvingTelemetry(version, testbed, ssh_client);
}

}  // namespace pins_test

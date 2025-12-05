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
#include "tests/integration/system/nsf/component_validators/swss_validator.h"

#include <string>

#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/ascii.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "gutil/gutil/status.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/ssh_client.h"

namespace pins_test {
namespace {

constexpr absl::string_view k31JulyRelease = "pins_release_20240731";
constexpr absl::string_view k02SeptRelease = "pins_release_20240902";

// The following objects will always be modified after APPLY_VIEW.
const absl::flat_hash_set<absl::string_view> kAllowList =
    absl::flat_hash_set<absl::string_view>({
        "SAI_OBJECT_TYPE_DEBUG_COUNTER",
        "SAI_OBJECT_TYPE_VIRTUAL_ROUTER",
    });

}  // namespace

//  Checks sairedis.rec file matches in SUT after APPLY_VIEW.
//  Filters records starting at timestamp after APPLY_VIEW.
//  Scans sairedis.rec and sairedis.rec.n (if it exists) for write operations on
//  SAI objects in the record file.
absl::Status SwssValidator::VerifySairedisRecOnNsfReboot(
    absl::string_view version, const Testbed& testbed,
    thinkit::SSHClient& ssh_client) {
  // Add always expected objects in the allow list.
  absl::flat_hash_set<absl::string_view> allowlist = kAllowList;
  // Add release specific objects in the allow list.
  if (!allowlist_.empty()) {
    allowlist.insert(allowlist_.begin(), allowlist_.end());
    allowlist_.clear();
  }

  std::string allowlist_str;
  for (const auto obj : allowlist) {
    absl::StrAppend(&allowlist_str, obj, ", ");
  }
  LOG(INFO) << "Allowlist for APPLY_VIEW: " << allowlist_str;

  constexpr absl::Duration kRunCommandTimeout = absl::Minutes(2);
  constexpr char kSairedisRecFile[] = "/var/log/tmp/or-con/swss/sairedis.rec";
  constexpr char kSairedisRecTmpFile[] = "/tmp/sairedis.rec.tmp";

  constexpr char kUnzipSairedisRecNCommands[] =
      "cp /var/log/tmp/or-con/swss/sairedis.rec.*.gz /tmp && gzip -d "
      "/tmp/sairedis.rec.*.gz";
  constexpr char kListSairedisRecNCommands[] =
      "ls /tmp/sairedis.rec.* | sort -t \'.\' -k 3nr";
  constexpr char kGenerateSairedisRecTmpCommands[] = "cat $0 $1 > $2";
  constexpr char kCleanupSairedisTmpCommands[] = "rm -f $0 $1";
  constexpr char kLastApplyViewCommands[] =
      "awk \'/APPLY_VIEW/ { line = $$0 } END { print line }\' $0";
  constexpr char kSairedisRecCheckerCommands[] =
      "awk \'/$0/,EOF {print;}\' $1 | "
      "grep \'|[s|S|c|C|r|R]|SAI_OBJECT_TYPE_\' | "
      "awk \'{ match($$0, /SAI_OBJECT_TYPE_[^:]*/) } { print substr( $$0, "
      "RSTART, RLENGTH )}\' | sort -u";

  LOG(INFO) << "Swss NSF Reboot Validation Start.";
  // Unzip /var/log/tmp/or-con/swss/sairedis.rec.*.gz file if exists.
  // The APPLY_VIEW line might be flushed to the archive file.
  auto response =
      ssh_client.RunCommand(GetSut(testbed).ChassisName(),
                            kUnzipSairedisRecNCommands, kRunCommandTimeout);
  // Concat sairedis.rec.n and sairedis.rec file to a sairedis.rec.tmp file if
  // rec.n files exit.
  std::string extra_sairedis_files;
  if (response.ok()) {
    ASSIGN_OR_RETURN(
        extra_sairedis_files,
        ssh_client.RunCommand(GetSut(testbed).ChassisName(),
                              kListSairedisRecNCommands, kRunCommandTimeout));
  }
  absl::StripAsciiWhitespace(&extra_sairedis_files);
  RETURN_IF_ERROR(
      ssh_client
          .RunCommand(GetSut(testbed).ChassisName(),
                      absl::Substitute(kGenerateSairedisRecTmpCommands,
                                       extra_sairedis_files, kSairedisRecFile,
                                       kSairedisRecTmpFile),
                      kRunCommandTimeout)
          .status());
  // Find last APPLY_VIEW entry in sairedis.rec.tmp file.
  ASSIGN_OR_RETURN(
      auto last_apply_view_entry,
      ssh_client.RunCommand(
          GetSut(testbed).ChassisName(),
          absl::Substitute(kLastApplyViewCommands, kSairedisRecTmpFile),
          kRunCommandTimeout));
  absl::StripAsciiWhitespace(&last_apply_view_entry);
  // Find SAI objects write operations after APPLY_VIEW in sairedis.rec.tmp
  // file.
  ASSIGN_OR_RETURN(
      auto sai_objects_list,
      ssh_client.RunCommand(
          GetSut(testbed).ChassisName(),
          absl::Substitute(
              kSairedisRecCheckerCommands,
              absl::StrReplaceAll(last_apply_view_entry, {{"|", "\\|"}}),
              kSairedisRecTmpFile),
          kRunCommandTimeout));
  LOG(INFO) << "Swss NSF Reboot Validation: sairedis.rec SET requests: "
            << sai_objects_list;
  // Cleanup sairedis.rec.* files.
  RETURN_IF_ERROR(ssh_client
                      .RunCommand(GetSut(testbed).ChassisName(),
                                  absl::Substitute(kCleanupSairedisTmpCommands,
                                                   kSairedisRecTmpFile,
                                                   extra_sairedis_files),
                                  kRunCommandTimeout)
                      .status());
  // Verify the write operations on SAI objects are in whitelist.
  absl::StripAsciiWhitespace(&sai_objects_list);
  std::string error_msg;
  if (last_apply_view_entry.empty()) {
    // Log error but return success. The fragility of the validation shouldn't
    // cause the validator to fail.
    LOG(ERROR) << "No APPLY_VIEW entry found in sairedis.rec file.";
    return absl::OkStatus();
  } else {
    for (const auto& sai_object : absl::StrSplit(sai_objects_list, '\n')) {
      if (!sai_object.empty() && !allowlist.contains(sai_object)) {
        absl::StrAppend(
            &error_msg,
            absl::Substitute(
                "SAI object type $0 is not in allow list that can have "
                "non-zero "
                "create/set/remove sairedis.rec entries during warm reboot.\n",
                sai_object));
      }
    }
  }
  if (!error_msg.empty()) {
    LOG(ERROR) << "Swss NSF Reboot Validation: " << error_msg;
    return absl::InternalError(error_msg);
  }
  return absl::OkStatus();
}

absl::Status SwssValidator::OnImageCopy(absl::string_view version,
                                        const Testbed& testbed,
                                        thinkit::SSHClient& ssh_client) {
  ASSIGN_OR_RETURN(auto sut_gnmi_stub, GetSut(testbed).CreateGnmiStub());
  ASSIGN_OR_RETURN(PinsSoftwareComponentInfo software_info,
                   GetPinsSoftwareComponentInfo(*sut_gnmi_stub));

  if (absl::StrContains(software_info.primary_network_stack.version,
                        k31JulyRelease) &&
      software_info.primary_network_stack.version !=
          software_info.secondary_network_stack.version) {
    LOG(INFO) << "Allowing additional APPLY_VIEW object operations during NSF "
                 "upgrade from "
              << k31JulyRelease << " to "
              << software_info.secondary_network_stack.version;
    allowlist_ = absl::flat_hash_set<absl::string_view>({
        // Objects set by CoppOrch.
        "SAI_OBJECT_TYPE_HOSTIF_TRAP_GROUP",
        "SAI_OBJECT_TYPE_HOSTIF",
        // Objects set by P4Orch ACL rule manager.
        "SAI_OBJECT_TYPE_HOSTIF_USER_DEFINED_TRAP",
        "SAI_OBJECT_TYPE_HOSTIF_TABLE_ENTRY",
    });
  }
  if (absl::StrContains(software_info.primary_network_stack.version,
                        k02SeptRelease) &&
      software_info.primary_network_stack.version !=
          software_info.secondary_network_stack.version) {
    LOG(INFO) << "Allowing additional APPLY_VIEW object operations during NSF "
                 "upgrade from "
              << k02SeptRelease << " to "
              << software_info.secondary_network_stack.version;
    allowlist_ = absl::flat_hash_set<absl::string_view>({
        "SAI_OBJECT_TYPE_SWITCH",
    });
  }
  return absl::OkStatus();
}

absl::Status SwssValidator::OnNsfReboot(absl::string_view version,
                                        const Testbed &testbed,
                                        thinkit::SSHClient &ssh_client) {
  return VerifySairedisRecOnNsfReboot(version, testbed, ssh_client);
}
}  // namespace pins_test

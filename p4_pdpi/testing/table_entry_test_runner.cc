// Copyright 2020 Google LLC
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

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/testing/test_helper.h"
#include "p4_pdpi/testing/union_main_p4_pd.pb.h"

using ::p4::config::v1::P4Info;

static void RunPiTableEntryTest(const pdpi::IrP4Info& info,
                                const std::string& test_name,
                                const p4::v1::TableEntry& pi) {
  RunGenericPiTest<pdpi::IrTableEntry, p4::v1::TableEntry>(
      info, test_name, pi,
      [](const pdpi::IrP4Info& info, const p4::v1::TableEntry& pi) {
        return pdpi::PiTableEntryToIr(info, pi, false);
      });
}

static void RunIrTableEntryTest(const pdpi::IrP4Info& info,
                                const std::string& test_name,
                                const pdpi::IrTableEntry& ir) {
  RunGenericIrToPiTest<pdpi::IrTableEntry, p4::v1::TableEntry>(
      info, test_name, ir,
      [](const pdpi::IrP4Info& info, const pdpi::IrTableEntry& ir) {
        return IrTableEntryToPi(info, ir, false);
      });
}

static void RunPdTableEntryTest(const pdpi::IrP4Info& info,
                                const std::string& test_name,
                                const pdpi::TableEntry& pd,
                                InputValidity validity, bool key_only = false) {
  RunGenericPdTest<pdpi::TableEntry, pdpi::IrTableEntry, p4::v1::TableEntry>(
      info, test_name, pd,
      [&](const pdpi::IrP4Info& ir_p4info,
          const google::protobuf::Message& pd) {
        return pdpi::PdTableEntryToIr(ir_p4info, pd, key_only);
      },
      [&](const pdpi::IrP4Info& ir_p4info, const pdpi::IrTableEntry& ir,
          google::protobuf::Message* pd) {
        return pdpi::IrTableEntryToPd(ir_p4info, ir, pd, key_only);
      },
      [&](const pdpi::IrP4Info& info, const pdpi::IrTableEntry& ir) {
        return pdpi::IrTableEntryToPi(info, ir, key_only);
      },
      [&](const pdpi::IrP4Info& info, const p4::v1::TableEntry& pi) {
        return pdpi::PiTableEntryToIr(info, pi, key_only);
      },
      [&](const pdpi::IrP4Info& info, const google::protobuf::Message& pd) {
        return pdpi::PdTableEntryToPi(info, pd, key_only);
      },
      [&](const pdpi::IrP4Info& info, const p4::v1::TableEntry& pi,
          google::protobuf::Message* pd) {
        return pdpi::PiTableEntryToPd(info, pi, pd, key_only);
      },
      validity,
      [&](const pdpi::IrP4Info& info, const pdpi::TableEntry& pd) {
        if (key_only) {
          pdpi::TableEntry key_only_pd;
          auto res = pdpi::PdTableEntryToOnlyKeyPd(info, pd, &key_only_pd);
          if (res.ok()) {
            return key_only_pd;
          } else {
            Fail(test_name,
                 "Unable to extract only the key part from PD table entry");
          }
        }
        return pd;
      });
}

static void RunPiTests(const pdpi::IrP4Info info) {
  RunPiTableEntryTest(info, "empty PI",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(""));

  RunPiTableEntryTest(info, "invalid table id",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 431
                      )pb"));

  RunPiTableEntryTest(info, "missing matches",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                      )pb"));

  RunPiTableEntryTest(info, "invalid match type - expect exact",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 1
                          lpm { value: "\xff\x22" prefix_len: 24 }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "invalid match type - expect lpm",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554436
                        match {
                          field_id: 1
                          ternary { value: "\xff\x22" mask: "\xd3\x54\x12" }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "invalid match type - expect ternary",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        priority: 32
                      )pb"));

  RunPiTableEntryTest(info, "invalid match type - expect optional",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554441
                        match {
                          field_id: 1
                          lpm { value: "\xff\x22" prefix_len: 24 }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "invalid match field id",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 11
                          exact { value: "\xff\x22" }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "invalid bytestring value",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 2
                          exact { value: "\xff\x22\x43\x45\x32" }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "invalid prefix length",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554436
                        match {
                          field_id: 1
                          lpm { value: "\xff\x22" prefix_len: 40 }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "duplicate match field id",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        match {
                          field_id: 1
                          exact { value: "\x10\x24\x32\x52" }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "lpm value - masked bits set",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554436
                        match {
                          field_id: 1
                          lpm { value: "\x10\x43\x23\x12" prefix_len: 24 }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "ternary value too long",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 1
                          ternary { value: "\x42\x12" mask: "\xff" }
                        }
                        priority: 32
                      )pb"));
  RunPiTableEntryTest(info, "ternary IPv6 64-bit value too long",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 6
                          ternary {
                            value: "\x01\x00\x00\x00\x00\x00\x00\x00\x00"
                            mask: "\x01\xff\xff\xff\xff\xff\xff\xff\xff"
                          }
                        }
                        priority: 32
                      )pb"));
  RunPiTableEntryTest(info, "ternary IPv6 63-bit value too long",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 7
                          ternary {
                            value: "\x80\x00\x00\x00\x00\x00\x00\x00"
                            mask: "\xff\xff\xff\xff\xff\xff\xff\xff"
                          }
                        }
                        priority: 32
                      )pb"));
  RunPiTableEntryTest(info, "ternary value and mask too long",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 1
                          ternary { value: "\x42\x12" mask: "\xff\xff" }
                        }
                        priority: 32
                      )pb"));

  RunPiTableEntryTest(info, "ternary value - masked bits set",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 1
                          ternary { value: "\x01\x00" mask: "\x00\xff" }
                        }
                        priority: 32
                      )pb"));

  RunPiTableEntryTest(info, "missing action",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        match {
                          field_id: 2
                          exact { value: "\x10\x24\x32\x52" }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "invalid action",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        match {
                          field_id: 2
                          exact { value: "\x10\x24\x32\x52" }
                        }
                        action { action_profile_member_id: 12 }
                      )pb"));

  RunPiTableEntryTest(info, "action set in table with action",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        match {
                          field_id: 2
                          exact { value: "\x10\x24\x32\x52" }
                        }
                        action {
                          action_profile_action_set {
                            action_profile_actions {
                              action {
                                action_id: 16777217
                                params { param_id: 1 value: "\000\000\000\010" }
                                params { param_id: 2 value: "\000\000\000\011" }
                              }
                              weight: 1
                            }
                          }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "action in table with action set",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554438
                        match {
                          field_id: 1
                          lpm { value: "\xff\x00" prefix_len: 24 }
                        }
                        action {
                          action {
                            action_id: 16777217
                            params { param_id: 1 value: "\000\000\000\010" }
                            params { param_id: 2 value: "\000\000\000\011" }
                          }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "missing action id",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        match {
                          field_id: 2
                          exact { value: "\x10\x24\x32\x52" }
                        }
                        action { action { action_id: 1 } }
                      )pb"));

  RunPiTableEntryTest(info, "invalid action id",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        match {
                          field_id: 2
                          exact { value: "\x10\x24\x32\x52" }
                        }
                        action { action { action_id: 16777219 } }
                      )pb"));

  RunPiTableEntryTest(info, "missing action params",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        match {
                          field_id: 2
                          exact { value: "\x10\x24\x32\x52" }
                        }
                        action {
                          action {
                            action_id: 16777217
                            params { param_id: 1 value: "\x54" }
                          }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "duplicate action param id",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        match {
                          field_id: 2
                          exact { value: "\x10\x24\x32\x52" }
                        }
                        action {
                          action {
                            action_id: 16777217
                            params { param_id: 1 value: "\x54" }
                            params { param_id: 1 value: "\x65" }
                          }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "invalid action param id",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554433
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        match {
                          field_id: 2
                          exact { value: "\x10\x24\x32\x52" }
                        }
                        action {
                          action {
                            action_id: 16777217
                            params { param_id: 67 value: "\x54" }
                            params { param_id: 2 value: "\x23" }
                          }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "zero lpm prefix length",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554436
                        match {
                          field_id: 1
                          lpm { value: "\x10\x32\x41\x5" prefix_len: 0 }
                        }
                        action { action { action_id: 21257015 } }
                      )pb"));

  RunPiTableEntryTest(info, "zero ternary mask",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 1
                          ternary { value: "\x01\x00" mask: "\x00" }
                        }
                        priority: 32
                        action {
                          action {
                            action_id: 16777219
                            params { param_id: 1 value: "\x54" }
                            params { param_id: 2 value: "\x23" }
                          }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "zero priority",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 1
                          ternary { value: "\x01\x00" mask: "\x01\xff" }
                        }
                        priority: 0
                        action {
                          action {
                            action_id: 16777219
                            params { param_id: 1 value: "\x54" }
                            params { param_id: 2 value: "\x23" }
                          }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "negative priority",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 1
                          ternary { value: "\x01\x00" mask: "\x01\xff" }
                        }
                        priority: -32
                        action {
                          action {
                            action_id: 16777219
                            params { param_id: 1 value: "\x54" }
                            params { param_id: 2 value: "\x23" }
                          }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "absent priority",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 1
                          ternary { value: "\x01\x00" mask: "\x01\xff" }
                        }
                        action {
                          action {
                            action_id: 16777219
                            params { param_id: 1 value: "\x54" }
                            params { param_id: 2 value: "\x23" }
                          }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "unexpected priority",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554436
                        match {
                          field_id: 1
                          lpm { value: "\x10\x32\x41\x00" prefix_len: 24 }
                        }
                        priority: 32
                        action { action { action_id: 21257015 } }
                      )pb"));

  RunPiTableEntryTest(info, "action set with negative weight",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554438
                        match {
                          field_id: 1
                          lpm { value: "\xff\x00" prefix_len: 24 }
                        }
                        action {
                          action_profile_action_set {
                            action_profile_actions {
                              action {
                                action_id: 16777217
                                params { param_id: 1 value: "\000\000\000\010" }
                                params { param_id: 2 value: "\000\000\000\011" }
                              }
                              weight: -1
                            }
                          }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "action set with invalid action",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554438
                        match {
                          field_id: 1
                          lpm { value: "\xff\x00" prefix_len: 24 }
                        }
                        action {
                          action_profile_action_set {
                            action_profile_actions {
                              action {
                                action_id: 16777218
                                params { param_id: 1 value: "\000\000\000\010" }
                                params { param_id: 2 value: "\000\000\000\011" }
                              }
                              weight: 1
                            }
                          }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "counter in a table with no counters",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554438
                        match {
                          field_id: 1
                          lpm { value: "\xff\x00" prefix_len: 24 }
                        }
                        action {
                          action_profile_action_set {
                            action_profile_actions {
                              action {
                                action_id: 16777217
                                params { param_id: 1 value: "\000\000\000\010" }
                                params { param_id: 2 value: "\000\000\000\011" }
                              }
                              weight: 24
                            }
                          }
                        }
                        counter_data { byte_count: 4213 }
                      )pb"));
  RunPiTableEntryTest(info, "action in a table with no actions defined",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554445
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        match {
                          field_id: 2
                          exact { value: "\x10\x24\x32\x52" }
                        }
                        action { action_profile_member_id: 12 }
                      )pb"));

  RunPiTableEntryTest(info, "unsupported table used",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554447
                        match {
                          field_id: 1
                          exact { value: "\xff\x22" }
                        }
                        match {
                          field_id: 2
                          exact { value: "\x10\x24\x32\x52" }
                        }
                      )pb"));

  RunPiTableEntryTest(info, "ternary table - unsupported action used",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 1
                          ternary { value: "\xd0" mask: "\x00\xff" }
                        }
                        action { action { action_id: 16777223 } }
                        priority: 32
                      )pb"));

  RunPiTableEntryTest(info, "ternary table - unsupported match field used",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554435
                        match {
                          field_id: 1
                          ternary { value: "\xd0" mask: "\x00\xff" }
                        }
                        match {
                          field_id: 5
                          ternary { value: "0" }
                        }
                        priority: 32
                      )pb"));

  RunPiTableEntryTest(info, "meter counter data but missing meter config",
                      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
                        table_id: 33554439
                        match {
                          field_id: 1
                          lpm { value: "\020$2\000" prefix_len: 24 }
                        }
                        action { action { action_id: 16777220 } }
                        counter_data { byte_count: 567 packet_count: 789 }
                        meter_counter_data {
                          green { byte_count: 568 packet_count: 790 }
                          yellow { byte_count: 569 packet_count: 791 }
                          red { byte_count: 570 packet_count: 792 }
                        }
                      )pb"));
  RunPiTableEntryTest(
      info, "meter counter data in a table with no meters",
      gutil::ParseProtoOrDie<p4::v1::TableEntry>(R"pb(
        table_id: 33554440
        match {
          field_id: 1
          lpm { value: "\020$2\000" prefix_len: 24 }
        }
        action { action { action_id: 16777220 } }
        meter_config { cir: 123 cburst: 345 pir: 123 pburst: 345 }
        counter_data { byte_count: 567 packet_count: 789 }
        meter_counter_data {}
      )pb"));
}  // NOLINT(readability/fn_size)

static void RunIrNoActionTableTests(const pdpi::IrP4Info& info) {
  // This function is defined separately and called from RunIrTests
  // since LINT complains if a function exceeds 500 lines.
  RunIrTableEntryTest(info, "action in a table with no actions defined",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "no_action_table"
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                        matches {
                          name: "ipv4"
                          exact { ipv4: "10.24.32.52" }
                        }
                        action {
                          name: "do_thing_1"
                          params {
                            name: "arg2"
                            value { hex_str: "0x01234567" }
                          }
                        })pb"));
}

static void RunIrTernaryTableTests(const pdpi::IrP4Info info) {
  RunIrTableEntryTest(info, "unsupported table used",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "unsupported_table"
                        matches {
                          name: "ipv4"
                          exact { ipv4: "10.10.10.10" }
                        }
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                      )pb"));
  RunIrTableEntryTest(info, "ternary table - unsupported action used",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "ternary_table"
                        matches {
                          name: "normal"
                          ternary { value { hex_str: "0x00" } }
                        }
                        action { name: "unsupported_action" }
                        priority: 32
                      )pb"));
  RunIrTableEntryTest(info, "ternary table - unsupported match field used",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "ternary_table"
                        matches {
                          name: "unsupported_field"
                          ternary { value { hex_str: "0x00" } }
                        }
                        priority: 32
                      )pb"));
}

static void RunIrMeterCounterTableEntryTests(const pdpi::IrP4Info& info) {
  RunIrTableEntryTest(info, "meter counter data in a table with no counters",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "wcmp_table"
                        matches {
                          name: "ipv4"
                          lpm {
                            value { ipv4: "0.0.255.0" }
                            prefix_length: 24
                          }
                        }
                        action_set {
                          actions {
                            action {
                              name: "do_thing_1"
                              params {
                                name: "arg2"
                                value { hex_str: "0x00000008" }
                              }
                              params {
                                name: "arg1"
                                value { hex_str: "0x00000009" }
                              }
                            }
                            weight: 24
                          }
                        }
                        meter_counter_data {
                          green { byte_count: 568 packet_count: 790 }
                          yellow { byte_count: 569 packet_count: 791 }
                          red { byte_count: 570 packet_count: 792 }
                        }
                      )pb"));
  RunIrTableEntryTest(info, "meter counter data but missing meter config",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "count_and_meter_table"
                        matches {
                          name: "ipv4"
                          lpm {
                            value { ipv4: "16.36.50.0" }
                            prefix_length: 24
                          }
                        }
                        action { name: "count_and_meter" }
                        counter_data { byte_count: 567 packet_count: 789 }
                        meter_counter_data {
                          green { byte_count: 568 packet_count: 790 }
                          yellow { byte_count: 569 packet_count: 791 }
                          red { byte_count: 570 packet_count: 792 }
                        }
                      )pb"));
}

static void RunIrTests(const pdpi::IrP4Info info) {
  RunIrTableEntryTest(info, "empty IR",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(""));

  RunIrTableEntryTest(info, "invalid table name",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "invalid"
                      )pb"));

  RunIrTableEntryTest(info, "missing matches",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                      )pb"));

  RunIrTableEntryTest(info, "invalid match type - expect exact",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "ipv6"
                          lpm {
                            value { ipv6: "::ff22" }
                            prefix_length: 96
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "invalid match type - expect optional",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "optional_table"
                        matches {
                          name: "ipv6"
                          lpm {
                            value { ipv6: "::ff22" }
                            prefix_length: 96
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "invalid match type - expect lpm",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "lpm2_table"
                        matches {
                          name: "ipv6"
                          ternary {
                            value { ipv6: "::ff22" }
                            mask { ipv6: "::00d3:5412" }
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "invalid match type - expect ternary",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "ternary_table"
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                        priority: 32
                      )pb"));

  RunIrTableEntryTest(
      info, "invalid value - address not in bounds for upper 64 bits of ipv6",
      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
        table_name: "ternary_table"
        matches {
          name: "ipv6_upper_64_bits"
          ternary {
            value { ipv6: "::ff22" }
            mask { ipv6: "::ffff" }
          }
        }
        priority: 32
      )pb"));

  RunIrTableEntryTest(
      info, "invalid value - address not in bounds for upper 63 bits of ipv6",
      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
        table_name: "ternary_table"
        matches {
          name: "ipv6_upper_63_bits"
          ternary {
            value { ipv6: "ff::" }
            mask { ipv6: "ffff:ffff:ffff:ffff::" }
          }
        }
        priority: 32
      )pb"));

  RunIrTableEntryTest(info, "invalid match field name",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "invalid"
                          exact { ipv6: "::ff22" }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "invalid IR value",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "ipv4"
                          exact { ipv6: "::ff22" }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "invalid prefix length",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "lpm1_table"
                        matches {
                          name: "ipv4"
                          lpm {
                            value { ipv4: "10.32.14.2" }
                            prefix_length: 40
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "duplicate match field name",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                        matches {
                          name: "ipv6"
                          exact { ipv4: "10.24.32.52" }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "lpm value - masked bits set",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "lpm1_table"
                        matches {
                          name: "ipv4"
                          lpm {
                            value { ipv4: "10.43.23.12" }
                            prefix_length: 24
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "ternary value too long",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "ternary_table"
                        matches {
                          name: "normal"
                          ternary {
                            value { hex_str: "0x4212" }
                            mask { hex_str: "0x00ff" }
                          }
                        }
                        priority: 32
                      )pb"));

  RunIrTableEntryTest(info, "ternary value and mask too long",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "ternary_table"
                        matches {
                          name: "normal"
                          ternary {
                            value { hex_str: "0x4212" }
                            mask { hex_str: "0x0fff" }
                          }
                        }
                        priority: 32
                      )pb"));

  RunIrTableEntryTest(info, "ternary value - masked bits set",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "ternary_table"
                        matches {
                          name: "ipv6"
                          ternary {
                            value { ipv6: "::0100" }
                            mask { ipv6: "::00ff" }
                          }
                        }
                        priority: 32
                      )pb"));

  RunIrTableEntryTest(info, "Invalid match field format",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "ternary_table"
                        matches {
                          name: "ipv6"
                          ternary {
                            value { ipv4: "127.0.0.0" }
                            mask { ipv4: "127.0.0.0" }
                          }
                        }
                        priority: 32
                      )pb"));

  RunIrTableEntryTest(info, "missing action",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                        matches {
                          name: "ipv4"
                          exact { ipv4: "10.24.32.52" }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "missing action name",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                        matches {
                          name: "ipv4"
                          exact { ipv4: "10.24.32.52" }
                        }
                        action {}
                      )pb"));

  RunIrTableEntryTest(info, "invalid action name",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                        matches {
                          name: "ipv4"
                          exact { ipv4: "10.24.32.52" }
                        }
                        action { name: "invalid" }
                      )pb"));

  RunIrTableEntryTest(info, "missing action params",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                        matches {
                          name: "ipv4"
                          exact { ipv4: "10.24.32.52" }
                        }
                        action {
                          name: "do_thing_1"
                          params {
                            name: "arg2"
                            value { hex_str: "0x01234567" }
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "duplicate action param name",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                        matches {
                          name: "ipv4"
                          exact { ipv4: "10.24.32.52" }
                        }
                        action {
                          name: "do_thing_1"
                          params {
                            name: "arg2"
                            value { hex_str: "0x01234567" }
                          }
                          params {
                            name: "arg2"
                            value { hex_str: "0x01234568" }
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "bad action param format",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                        matches {
                          name: "ipv4"
                          exact { ipv4: "10.24.32.52" }
                        }
                        action {
                          name: "do_thing_1"
                          params {
                            name: "arg1"
                            value { ipv6: "ffff::" }
                          }
                          params {
                            name: "arg2"
                            value { str: "0x01234567" }
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "invalid action param name",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                        matches {
                          name: "ipv4"
                          exact { ipv4: "10.24.32.52" }
                        }
                        action {
                          name: "do_thing_1"
                          params {
                            name: "arg"
                            value { hex_str: "0x01234567" }
                          }
                          params {
                            name: "arg1"
                            value { hex_str: "0x01234568" }
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "action set in table with action",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "id_test_table"
                        matches {
                          name: "ipv6"
                          exact { ipv6: "::ff22" }
                        }
                        matches {
                          name: "ipv4"
                          exact { ipv4: "10.24.32.52" }
                        }
                        action_set {
                          actions {
                            action {
                              name: "do_thing_1"
                              params {
                                name: "arg2"
                                value { hex_str: "0x01234567" }
                              }
                              params {
                                name: "arg1"
                                value { hex_str: "0x01234568" }
                              }
                            }
                            weight: 1
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "action in table with action set",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "wcmp_table"
                        matches {
                          name: "ipv4"
                          lpm {
                            value { ipv4: "34.234.42.0" }
                            prefix_length: 24
                          }
                        }
                        action {
                          name: "do_thing_1"
                          params {
                            name: "arg2"
                            value { hex_str: "0x01234567" }
                          }
                          params {
                            name: "arg1"
                            value { hex_str: "0x01234568" }
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "zero lpm prefix length",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "lpm1_table"
                        matches {
                          name: "ipv4"
                          lpm {
                            value { ipv4: "10.32.41.5" }
                            prefix_length: 0
                          }
                        }
                        action { name: "NoAction" }
                      )pb"));

  RunIrTableEntryTest(info, "zero ternary mask",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "ternary_table"
                        matches {
                          name: "normal"
                          ternary {
                            value { hex_str: "0x100" }
                            mask { hex_str: "0x000" }
                          }
                        }
                        priority: 32
                        action {
                          name: "do_thing_1"
                          params {
                            name: "arg2"
                            value { hex_str: "0x01234567" }
                          }
                          params {
                            name: "arg1"
                            value { hex_str: "0x01234568" }
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "zero priority",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "ternary_table"
                        matches {
                          name: "normal"
                          ternary {
                            value { hex_str: "0x100" }
                            mask { hex_str: "0x1ff" }
                          }
                        }
                        priority: 0
                        action {
                          name: "do_thing_1"
                          params {
                            name: "arg2"
                            value { hex_str: "0x01234567" }
                          }
                          params {
                            name: "arg1"
                            value { hex_str: "0x01234568" }
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "negative priority",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "ternary_table"
                        matches {
                          name: "normal"
                          ternary {
                            value { hex_str: "0x100" }
                            mask { hex_str: "0x1ff" }
                          }
                        }
                        priority: -32
                        action {
                          name: "do_thing_1"
                          params {
                            name: "arg2"
                            value { hex_str: "0x01234567" }
                          }
                          params {
                            name: "arg1"
                            value { hex_str: "0x01234568" }
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "absent priority",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "ternary_table"
                        matches {
                          name: "normal"
                          ternary {
                            value { hex_str: "0x100" }
                            mask { hex_str: "0x1ff" }
                          }
                        }
                        action {
                          name: "do_thing_1"
                          params {
                            name: "arg2"
                            value { hex_str: "0x01234567" }
                          }
                          params {
                            name: "arg1"
                            value { hex_str: "0x01234568" }
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "unexpected priority",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "lpm1_table"
                        matches {
                          name: "ipv4"
                          lpm {
                            value { ipv4: "10.32.41.0" }
                            prefix_length: 24
                          }
                        }
                        priority: 32
                        action { name: "NoAction" }
                      )pb"));

  RunIrTableEntryTest(info, "action set with negative weight",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "wcmp_table"
                        matches {
                          name: "ipv4"
                          lpm {
                            value { ipv4: "0.0.255.0" }
                            prefix_length: 24
                          }
                        }
                        action_set {
                          actions {
                            action {
                              name: "do_thing_1"
                              params {
                                name: "arg2"
                                value { hex_str: "0x00000008" }
                              }
                              params {
                                name: "arg1"
                                value { hex_str: "0x00000009" }
                              }
                            }
                            weight: -1
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "action set with invalid action",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "wcmp_table"
                        matches {
                          name: "ipv4"
                          lpm {
                            value { ipv4: "0.0.255.0" }
                            prefix_length: 24
                          }
                        }
                        action_set {
                          actions {
                            action {
                              name: "invalid_do_thing_1"
                              params {
                                name: "arg2"
                                value { hex_str: "0x00000008" }
                              }
                              params {
                                name: "arg1"
                                value { hex_str: "0x00000009" }
                              }
                            }
                            weight: -1
                          }
                        }
                      )pb"));

  RunIrTableEntryTest(info, "counter in a table with no counters",
                      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
                        table_name: "wcmp_table"
                        matches {
                          name: "ipv4"
                          lpm {
                            value { ipv4: "0.0.255.0" }
                            prefix_length: 24
                          }
                        }
                        action_set {
                          actions {
                            action {
                              name: "do_thing_1"
                              params {
                                name: "arg2"
                                value { hex_str: "0x00000008" }
                              }
                              params {
                                name: "arg1"
                                value { hex_str: "0x00000009" }
                              }
                            }
                            weight: 24
                          }
                        }
                        counter_data { byte_count: 4213 }
                      )pb"));
  RunIrNoActionTableTests(info);
  RunIrTernaryTableTests(info);
  RunIrMeterCounterTableEntryTests(info);
}  // NOLINT(readability/fn_size)

static void RunPdMeterCounterTableEntryTests(const pdpi::IrP4Info& info) {
  RunPdTableEntryTest(
      info, "table entry with a meter counter data (packet counter)",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        packet_count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { packet_count_and_meter {} }
          meter_config { bytes_per_second: 123 burst_bytes: 345 }
          counter_data { packet_count: 789 }
          meter_counter_data {
            green { packet_count: 790 }
            yellow { packet_count: 791 }
            red { packet_count: 792 }
          }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "table entry with a meter counter data (byte counter)",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        byte_count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { byte_count_and_meter {} }
          meter_config { bytes_per_second: 123 burst_bytes: 345 }
          counter_data { byte_count: 567 }
          meter_counter_data {
            green { byte_count: 568 }
            yellow { byte_count: 569 }
            red { byte_count: 570 }
          }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "table entry with counters, meters and meter counter data",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          meter_config { bytes_per_second: 123 burst_bytes: 345 }
          counter_data { byte_count: 567 packet_count: 789 }
          meter_counter_data {
            green { byte_count: 568 packet_count: 790 }
            yellow { byte_count: 569 packet_count: 791 }
            red { byte_count: 570 packet_count: 792 }
          }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "table entry with counters, meter counter data but no meter config",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          counter_data { byte_count: 567 packet_count: 789 }
          meter_counter_data {
            green { byte_count: 568 packet_count: 790 }
            yellow { byte_count: 569 packet_count: 791 }
            red { byte_count: 570 packet_count: 792 }
          }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "table entry with meter counter data but no color counters",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          meter_config { bytes_per_second: 123 burst_bytes: 345 }
          counter_data { byte_count: 567 packet_count: 789 }
          meter_counter_data {}
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "table entry with meter counter data but missing some colors",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          meter_config { bytes_per_second: 123 burst_bytes: 345 }
          counter_data { byte_count: 567 packet_count: 789 }
          meter_counter_data {
            green { byte_count: 568 packet_count: 790 }
            red { byte_count: 570 packet_count: 792 }
          }
        }
      )pb"),
      INPUT_IS_VALID);
}

static void RunPdTests(const pdpi::IrP4Info info) {
  RunPdTableEntryTest(info, "empty PD",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(""),
                      INPUT_IS_INVALID);

  RunPdTableEntryTest(info, "missing matches",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        id_test_table_entry {}
                      )pb"),
                      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "missing action", gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        id_test_table_entry { match { ipv6: "::ff22" ipv4: "16.36.50.82" } }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(info, "exact match missing",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        id_test_table_entry {
                          match { ipv6: "::ff22" }
                          action {
                            do_thing_2 {
                              normal: "0x054"
                              ipv4: "10.43.12.5"
                              ipv6: "3242::fee2"
                              mac: "00:11:22:33:44:55"
                              str: "hello"
                            }
                          }
                        }
                      )pb"),
                      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "negative prefix length",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        lpm2_table_entry {
          match { ipv6 { value: "ffff::abcd:0:0" prefix_length: -4 } }
          action { NoAction {} }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "prefix length too large",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        lpm2_table_entry {
          match { ipv6 { value: "ffff::abcd:0:0" prefix_length: 132 } }
          action { NoAction {} }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "zero prefix length", gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        lpm2_table_entry {
          match { ipv6 { value: "ffff::abcd:0:0" prefix_length: 0 } }
          action { NoAction {} }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "ternary entry with zero mask",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match {
            normal { value: "0x052" mask: "0x000" }
            ipv4 { value: "10.43.12.4" mask: "10.43.12.5" }
            ipv6 { value: "::ee66" mask: "::ff77" }
            mac { value: "11:22:33:44:55:66" mask: "33:66:77:66:77:77" }
          }
          priority: 32
          action { do_thing_3 { arg1: "0x23" arg2: "0x0251" } }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "lpm value - masked bits set",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        lpm2_table_entry {
          match { ipv6 { value: "ffff::abcd:0:aabb" prefix_length: 96 } }
          action { NoAction {} }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "ternary value - masked bits set",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match {
            normal { value: "0x052" mask: "0x001" }
            ipv4 { value: "10.43.12.4" mask: "10.43.12.5" }
            ipv6 { value: "::ee66" mask: "::ff77" }
            mac { value: "11:22:33:44:55:66" mask: "33:66:77:66:77:77" }
          }
          priority: 32
          action { do_thing_3 { arg1: "0x23" arg2: "0x0251" } }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "action with missing arguments",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        id_test_table_entry {
          match { ipv6: "::ff22" ipv4: "16.36.50.82" }
          action {
            do_thing_2 { normal: "0x054" mac: "00:11:22:33:44:55" str: "hello" }
          }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(info, "action with wrong argument format",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        id_test_table_entry {
                          match { ipv6: "::ff22" ipv4: "16.36.50.82" }
                          action {
                            do_thing_2 {
                              normal: "10.23.43.1"
                              ipv4: "10.43.12.5"
                              ipv6: "3242::fee2"
                              mac: "00:11:22:33:44:55"
                              str: "hello"
                            }
                          }
                        }
                      )pb"),
                      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "ternary table with zero priority",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match {
            normal { value: "0x052" mask: "0x273" }
            ipv4 { value: "10.43.12.4" mask: "10.43.12.5" }
            ipv6 { value: "::ee66" mask: "::ff77" }
            mac { value: "11:22:33:44:55:66" mask: "33:66:77:66:77:77" }
          }
          priority: 0
          action { do_thing_3 { arg1: "0x23" arg2: "0x0251" } }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "ternary table with negative priority",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match {
            normal { value: "0x052" mask: "0x273" }
            ipv4 { value: "10.43.12.4" mask: "10.43.12.5" }
            ipv6 { value: "::ee66" mask: "::ff77" }
            mac { value: "11:22:33:44:55:66" mask: "33:66:77:66:77:77" }
          }
          priority: -43
          action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "ternary table with priority absent",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match {
            normal { value: "0x052" mask: "0x273" }
            ipv4 { value: "10.43.12.4" mask: "10.43.12.5" }
            ipv6 { value: "::ee66" mask: "::ff77" }
            mac { value: "11:22:33:44:55:66" mask: "33:66:77:66:77:77" }
          }
          action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "wcmp table with negative weight",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        wcmp_table_entry {
          match { ipv4 { value: "0.0.255.0" prefix_length: 24 } }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234567" arg1: "0x01234568" } }
            weight: -1
          }
        }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "valid wcmp table with choice of action",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        wcmp2_table_entry {
          match { ipv4 { value: "0.0.255.0" prefix_length: 24 } }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234567" arg1: "0x01234568" } }
            weight: 1
          }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234569" arg1: "0x01234560" } }
            weight: 2
          }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "valid wcmp table with watch_port",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        wcmp2_table_entry {
          match { ipv4 { value: "0.0.255.0" prefix_length: 24 } }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234567" arg1: "0x01234568" } }
            weight: 1
            watch_port: "abc"
          }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234569" arg1: "0x01234560" } }
            weight: 2
          }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "valid wcmp table", gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        wcmp_table_entry {
          match { ipv4 { value: "0.0.255.0" prefix_length: 24 } }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234567" arg1: "0x01234568" } }
            weight: 1
          }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234569" arg1: "0x01234560" } }
            weight: 2
          }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(info, "exact matches of all formats",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        exact_table_entry {
                          match {
                            normal: "0x054"
                            ipv4: "10.43.12.5"
                            ipv6: "3242::fee2"
                            mac: "00:11:22:33:44:55"
                            str: "hello"
                          }
                          action { NoAction {} }
                        }
                      )pb"),
                      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "valid optional table missing a match",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        optional_table_entry {
          match { ipv6 { value: "3242::fee2" } }
          action { do_thing_1 { arg2: "0x01234567" arg1: "0x01234568" } }
          priority: 32
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "ternary with wildcard",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match { normal { value: "0x052" mask: "0x273" } }
          priority: 32
          action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "metadata", gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match { normal { value: "0x052" mask: "0x273" } }
          priority: 32
          controller_metadata: "abc"
          action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "ternary table for all formats",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match {
            normal { value: "0x052" mask: "0x273" }
            ipv4 { value: "10.43.12.4" mask: "10.43.12.5" }
            ipv6 { value: "::ee66" mask: "::ff77" }
            ipv6_upper_64_bits {
              value: "0:1fff:ee66:aabb::"
              mask: "0:ffff:ffff:ffff::"
            }
            ipv6_upper_63_bits {
              value: "0:1fff:ee66:aafe::"
              mask: "0:ffff:ffff:fffe::"
            }
            mac { value: "11:22:33:44:55:66" mask: "33:66:77:66:77:77" }
          }
          priority: 32
          action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "ipv4 LPM table", gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        lpm1_table_entry {
          match { ipv4 { value: "10.43.12.0" prefix_length: 24 } }
          action { NoAction {} }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "ipv6 LPM table", gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        lpm2_table_entry {
          match { ipv6 { value: "ffff::abcd:0:0" prefix_length: 96 } }
          action { NoAction {} }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(info, "action with all formats as arguments",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        id_test_table_entry {
                          match { ipv6: "::ff22" ipv4: "16.36.50.82" }
                          action {
                            do_thing_2 {
                              normal: "0x054"
                              ipv4: "10.43.12.5"
                              ipv6: "3242::fee2"
                              mac: "00:11:22:33:44:55"
                              str: "hello"
                            }
                          }
                        }
                      )pb"),
                      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "table entry without counters and meters",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "table entry with a meter",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          meter_config { bytes_per_second: 123 burst_bytes: 345 }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "table entry with a byte counter",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          counter_data { byte_count: 567 }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "table entry with a packet counter",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          counter_data { packet_count: 789 }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "table entry with a counter (both units)",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          counter_data { byte_count: 567 packet_count: 789 }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info, "table entry with counters and meters",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          meter_config { bytes_per_second: 123 burst_bytes: 345 }
          counter_data { byte_count: 567 packet_count: 789 }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(info, "exact match with empty string for Format::STRING",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        exact_table_entry {
                          match {
                            normal: "0x054"
                            ipv4: "10.43.12.5"
                            ipv6: "3242::fee2"
                            mac: "00:11:22:33:44:55"
                            str: ""
                          }
                          action { NoAction {} }
                        }
                      )pb"),
                      INPUT_IS_VALID);

  RunPdTableEntryTest(info, "ipv4 LPM table with /0",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        lpm1_table_entry {
                          match {}
                          action { NoAction {} }
                        }
                      )pb"),
                      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info,
      "exact match with string containing null characters for Format::STRING",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        exact_table_entry {
          match {
            normal: "0x054"
            ipv4: "10.43.12.5"
            ipv6: "3242::fee2"
            mac: "00:11:22:33:44:55"
            str: "\0001u"
          }
          action { NoAction {} }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info,
      "optional match with string containing null characters for "
      "Format::STRING",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        optional_table_entry {
          match { str { value: "\000324" } }
          action { do_thing_1 { arg2: "0x01234567" arg1: "0x01234568" } }
          priority: 32
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(
      info,
      "valid wcmp table with watch_port containing null characters for "
      "Format::STRING",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        wcmp2_table_entry {
          match { ipv4 { value: "0.0.255.0" prefix_length: 24 } }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234567" arg1: "0x01234568" } }
            weight: 1
            watch_port: "\00abc"
          }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234569" arg1: "0x01234560" } }
            weight: 2
          }
        }
      )pb"),
      INPUT_IS_VALID);

  RunPdTableEntryTest(info, "valid no action table",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        no_action_table_entry {
                          match { ipv6: "::ff22" ipv4: "16.36.50.82" }
                        })pb"),
                      INPUT_IS_VALID);

  RunPdTableEntryTest(info, "unsupported field in pd",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        optional_table_entry {
                          match {
                            mac { value: "00:11:22:33:44:55" }
                            ipv4 { value: "16.36.50.82" }
                          }
                        })pb"),
                      INPUT_IS_INVALID);

  RunPdMeterCounterTableEntryTests(info);
}

static void RunPdTestsOnlyKey(const pdpi::IrP4Info info) {
  RunPdTableEntryTest(info, "missing matches with key_only=true",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        id_test_table_entry {}
                      )pb"),
                      INPUT_IS_INVALID, /*key_only=*/true);

  RunPdTableEntryTest(
      info, "ternary table with priority absent with key_only=true",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match {
            normal { value: "0x052" mask: "0x273" }
            ipv4 { value: "10.43.12.4" mask: "10.43.12.5" }
            ipv6 { value: "::ee66" mask: "::ff77" }
            mac { value: "11:22:33:44:55:66" mask: "33:66:77:66:77:77" }
          }
          action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
        }
      )pb"),
      INPUT_IS_INVALID, /*key_only=*/true);

  RunPdTableEntryTest(
      info, "unsupported table used",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        unsupported_table_entry { match { ipv4: "10.10.10.10" ipv6: "::ff22" } }
      )pb"),
      INPUT_IS_INVALID);

  RunPdTableEntryTest(info, "ternary table - unsupported action used",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        ternary_table_entry {
                          match { normal { value: "0x052" mask: "0x273" } }
                          priority: 32
                          action { unsupported_action {} }
                        }
                      )pb"),
                      INPUT_IS_INVALID);

  RunPdTableEntryTest(info, "ternary table - unsupported match field used",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        ternary_table_entry {
                          match { unsupported_field { value: "0x052" } }
                          priority: 32
                          action { do_thing_3 { arg1: "0x23" arg2: "0x0251" } }
                        }
                      )pb"),
                      INPUT_IS_INVALID);

  RunPdTableEntryTest(
      info, "ipv4 LPM table with key_only=true",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        lpm1_table_entry {
          match { ipv4 { value: "10.43.12.0" prefix_length: 24 } }
          action { NoAction {} }
        }
      )pb"),
      INPUT_IS_VALID, /*key_only=*/true);

  RunPdTableEntryTest(
      info, "ternary match with key_only=true",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match { normal { value: "0x052" mask: "0x273" } }
          priority: 32
          action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
        }
      )pb"),
      INPUT_IS_VALID, /*key_only=*/true);
}

int main(int argc, char** argv) {
  // Usage: table_entry_test <p4info file>.
  if (argc != 2) {
    std::cerr << "Invalid number of arguments." << std::endl;
    return 1;
  }
  const auto p4info =
      gutil::ParseProtoFileOrDie<p4::config::v1::P4Info>(argv[1]);

  absl::StatusOr<pdpi::IrP4Info> status_or_info = pdpi::CreateIrP4Info(p4info);
  if (!status_or_info.status().ok()) {
    std::cerr << "Unable to create IrP4Info." << std::endl;
    return 1;
  }
  pdpi::IrP4Info info = status_or_info.value();

  RunPiTests(info);
  RunIrTests(info);
  RunPdTests(info);
  RunPdTestsOnlyKey(info);
  return 0;
}

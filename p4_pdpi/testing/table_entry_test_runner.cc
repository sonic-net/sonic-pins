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

#include <iostream>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/testing/test_helper.h"
#include "p4_pdpi/testing/union_main_p4_pd.pb.h"
#include "p4_pdpi/translation_options.h"

using ::p4::config::v1::P4Info;

// Used to configure an IrTableEntryTest.
struct IrTestConfig {
  // Whether the test is expected to fail or not.
  InputValidity validity = INPUT_IS_INVALID;
  // Whether IR->PD should be tested or not.
  bool test_ir_to_pd = true;
};

static void RunPiEntityTest(const pdpi::IrP4Info& info,
                            const std::string& test_name,
                            const p4::v1::Entity& pi,
                            InputValidity validity = INPUT_IS_INVALID) {
  RunGenericPiTest<pdpi::IrEntity, p4::v1::Entity>(
      info, test_name, pi, pdpi::TranslationOptions(),
      [](const pdpi::IrP4Info& info, const p4::v1::Entity& pi,
         pdpi::TranslationOptions options) {
        return pdpi::PiEntityToIr(info, pi, options);
      },
      validity);
}

static void RunIrEntityTest(const pdpi::IrP4Info& info,
                            const std::string& test_name,
                            const pdpi::IrEntity& ir,
                            IrTestConfig config = IrTestConfig()) {
  RunGenericIrToPiTest<pdpi::IrEntity, p4::v1::Entity>(
      info, absl::StrCat(test_name, " (IR -> PI)"), ir,
      pdpi::TranslationOptions(),
      [](const pdpi::IrP4Info& info, const pdpi::IrEntity& ir,
         pdpi::TranslationOptions options) {
        return pdpi::IrEntityToPi(info, ir, options);
      },
      config.validity);
  if (config.test_ir_to_pd) {
    RunGenericIrToPdTest<pdpi::IrEntity, pdpi::TableEntry>(
        info, absl::StrCat(test_name, " (IR -> PD)"), ir,
        pdpi::TranslationOptions(),
        [](const pdpi::IrP4Info& info, const pdpi::IrEntity& ir,
           google::protobuf::Message* pd, pdpi::TranslationOptions options) {
          return pdpi::IrEntityToPdTableEntry(info, ir, pd, options);
        },
        config.validity);
  }
}

static void RunPdTableEntryTest(const pdpi::IrP4Info& info,
                                std::string test_name,
                                const pdpi::TableEntry& pd,
                                InputValidity validity,
                                pdpi::TranslationOptions options = {}) {
  absl::StrAppend(&test_name, "\n", options);
  RunGenericPdTest<pdpi::TableEntry, pdpi::IrEntity, p4::v1::Entity>(
      info, test_name, pd, options, pdpi::PdTableEntryToIrEntity,
      pdpi::IrEntityToPdTableEntry, pdpi::IrEntityToPi, pdpi::PiEntityToIr,
      pdpi::PdTableEntryToPiEntity, pdpi::PiEntityToPdTableEntry, validity,
      /*relevant_pd_fields=*/
      [&](const pdpi::IrP4Info& info, const pdpi::TableEntry& pd,
          pdpi::TranslationOptions options) {
        if (!options.key_only) return pd;
        pdpi::TableEntry key_only_pd;
        absl::Status status =
            pdpi::PdTableEntryToOnlyKeyPd(info, pd, &key_only_pd);
        if (!status.ok()) {
          Fail(test_name,
               "Unable to extract only the key part from PD table entry");
        }
        return key_only_pd;
      });
}

static void RunPiMulticastTest(const pdpi::IrP4Info& info) {
  RunPiEntityTest(info, "multicast group entry with deprecated egress_port set",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    packet_replication_engine_entry {
                      multicast_group_entry {
                        multicast_group_id: 7
                        replicas { egress_port: 3 instance: 1 }
                      }
                    }
                  )pb"));
  RunPiEntityTest(info, "multicast group entry with duplicate replica",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    packet_replication_engine_entry {
                      multicast_group_entry {
                        multicast_group_id: 7
                        replicas { port: "some_port" instance: 1 }
                        replicas { port: "some_port" instance: 1 }
                      }
                    }
                  )pb"));
  RunPiEntityTest(info, "valid multicast group entry",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    packet_replication_engine_entry {
                      multicast_group_entry {
                        multicast_group_id: 7
                        replicas { port: "some_port" instance: 1 }
                        replicas { port: "some_port" instance: 2 }
                        replicas { port: "some_other_port" instance: 1 }
                      }
                    }
                  )pb"),
                  /*validity=*/INPUT_IS_VALID);
  RunPiEntityTest(info, "valid multicast group entry without explicit instance",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    packet_replication_engine_entry {
                      multicast_group_entry {
                        multicast_group_id: 7
                        replicas { port: "some_port" }
                        replicas { port: "some_other_port" }
                      }
                    }
                  )pb"),
                  /*validity=*/INPUT_IS_VALID);
  RunPiEntityTest(
      info, "valid multicast group entry with backup replicas",
      gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 7
            replicas {
              port: "some_port"
              instance: 1
              backup_replicas { port: "some_other_port" instance: 2 }
              backup_replicas { port: "third_port" instance: 1 }
            }
            replicas {
              port: "some_other_port"
              instance: 1
              backup_replicas { port: "some_port" instance: 2 }
              backup_replicas { port: "third_port" instance: 2 }
            }
          }
        }
      )pb"),
      /*validity=*/INPUT_IS_VALID);
  RunPiEntityTest(
      info,
      "multicast group entry with a backup replica that has the same port as "
      "the primary replica",
      gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 7
            replicas {
              port: "some_port"
              instance: 1
              backup_replicas { port: "some_port" instance: 2 }
              backup_replicas { port: "some_other_port" instance: 2 }
            }
          }
        }
      )pb"));
   RunPiEntityTest(
      info,
      "multicast group entry with a backup replica that has the same port "
      "instance pair as another primary replica",
      gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 7
            replicas {
              port: "some_port"
              instance: 1
              backup_replicas { port: "some_other_port" instance: 2 }
            }
            replicas { port: "some_other_port" instance: 2 }
          }
        }
      )pb"));
   RunPiEntityTest(
      info,
      "multicast group entry with a backup replica that has the same port "
      "instance pair as another backup replica",
      gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 7
            replicas {
              port: "some_port"
              instance: 1
              backup_replicas { port: "some_other_port" instance: 2 }
            }
            replicas {
              port: "third_port"
              instance: 1
              backup_replicas { port: "some_other_port" instance: 2 }
            }
          }
        }
      )pb"));
}

static void RunPiCloneSessionTest(const pdpi::IrP4Info& info) {
  RunPiEntityTest(info, "valid clone session group entry",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    packet_replication_engine_entry {
                      clone_session_entry {
                        session_id: 7
                        replicas { port: "some_port" instance: 1 }
                        replicas { port: "some_port" instance: 2 }
                        replicas { port: "some_other_port" instance: 1 }
                        class_of_service: 2
                        packet_length_bytes: 200
                      }
                    }
                  )pb"),
                  /*validity=*/INPUT_IS_VALID);
  RunPiEntityTest(info, "clone session group entry with duplicate replica",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    packet_replication_engine_entry {
                      clone_session_entry {
                        session_id: 7
                        replicas { port: "some_port" instance: 1 }
                        replicas { port: "some_port" instance: 1 }
                        class_of_service: 2
                        packet_length_bytes: 200
                      }
                    }
                  )pb"),
                  /*validity=*/INPUT_IS_VALID);
  RunPiEntityTest(info, "valid clone session entry without explicit instance",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    packet_replication_engine_entry {
                      clone_session_entry {
                        session_id: 7
                        replicas { port: "some_port" }
                        replicas { port: "some_other_port" }
                        class_of_service: 2
                        packet_length_bytes: 200
                      }
                    }
                  )pb"),
                  /*validity=*/INPUT_IS_VALID);
}

static void RunPiTests(const pdpi::IrP4Info info) {
  RunPiEntityTest(info, "empty PI", gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                  )pb"));

  RunPiEntityTest(info, "empty table PI",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {}
                  )pb"));

  RunPiEntityTest(info, "invalid table id",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry { table_id: 431 }
                  )pb"));

  RunPiEntityTest(info, "missing matches",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry { table_id: 33554433 }
                  )pb"));

  RunPiEntityTest(info, "invalid match type - expect exact",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554433
                      match {
                        field_id: 1
                        lpm { value: "\xff\x22" prefix_len: 24 }
                      }
                    }
                  )pb"));

  RunPiEntityTest(info, "invalid match type - expect lpm",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554436
                      match {
                        field_id: 1
                        ternary { value: "\xff\x22" mask: "\xd3\x54\x12" }
                      }
                    }
                  )pb"));

  RunPiEntityTest(info, "invalid match type - expect ternary",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554435
                      match {
                        field_id: 1
                        exact { value: "\xff\x22" }
                      }
                      priority: 32
                    }
                  )pb"));

  RunPiEntityTest(info, "invalid match type - expect optional",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554441
                      match {
                        field_id: 1
                        lpm { value: "\xff\x22" prefix_len: 24 }
                      }
                    }
                  )pb"));

  RunPiEntityTest(info, "invalid match field id",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554433
                      match {
                        field_id: 11
                        exact { value: "\xff\x22" }
                      }
                    }
                  )pb"));

  RunPiEntityTest(info, "invalid bytestring value",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554433
                      match {
                        field_id: 2
                        exact { value: "\xff\x22\x43\x45\x32" }
                      }
                    }
                  )pb"));

  RunPiEntityTest(info, "empty bytestring in match field",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554441
                      match {
                        field_id: 3
                        optional { value: "" }
                      }
                      action {
                        action {
                          action_id: 16777217
                          params { param_id: 1 value: "\001#Eg" }
                          params { param_id: 2 value: "\001#Eh" }
                        }
                      }
                      priority: 32
                    }
                  )pb"));

  RunPiEntityTest(info, "empty bytestring in action parameter",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554441
                      match {
                        field_id: 3
                        optional { value: "hello" }
                      }
                      action {
                        action {
                          action_id: 16777217
                          params { param_id: 1 value: "" }
                          params { param_id: 2 value: "" }
                        }
                      }
                      priority: 32
                    }
                  )pb"));

  RunPiEntityTest(info, "invalid prefix length",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554436
                      match {
                        field_id: 1
                        lpm { value: "\xff\x22" prefix_len: 40 }
                      }
                    }
                  )pb"));

  RunPiEntityTest(info, "duplicate match field id",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554433
                      match {
                        field_id: 1
                        exact { value: "\xff\x22" }
                      }
                      match {
                        field_id: 1
                        exact { value: "\x10\x24\x32\x52" }
                      }
                    }
                  )pb"));

  RunPiEntityTest(info, "lpm value - masked bits set",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554436
                      match {
                        field_id: 1
                        lpm { value: "\x10\x43\x23\x12" prefix_len: 24 }
                      }
                    }
                  )pb"));

  RunPiEntityTest(info, "ternary value too long",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554435
                      match {
                        field_id: 1
                        ternary { value: "\x42\x12" mask: "\xff" }
                      }
                      priority: 32
                    }
                  )pb"));
  RunPiEntityTest(info, "ternary IPv6 64-bit value too long",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554435
                      match {
                        field_id: 6
                        ternary {
                          value: "\x01\x00\x00\x00\x00\x00\x00\x00\x00"
                          mask: "\x01\xff\xff\xff\xff\xff\xff\xff\xff"
                        }
                      }
                      priority: 32
                    }
                  )pb"));
  RunPiEntityTest(info, "ternary IPv6 63-bit value too long",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554435
                      match {
                        field_id: 7
                        ternary {
                          value: "\x80\x00\x00\x00\x00\x00\x00\x00"
                          mask: "\xff\xff\xff\xff\xff\xff\xff\xff"
                        }
                      }
                      priority: 32
                    }
                  )pb"));
  RunPiEntityTest(info, "ternary value and mask too long",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554435
                      match {
                        field_id: 1
                        ternary { value: "\x42\x12" mask: "\xff\xff" }
                      }
                      priority: 32
                    }
                  )pb"));

  RunPiEntityTest(info, "ternary value - masked bits set",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554435
                      match {
                        field_id: 1
                        ternary { value: "\x01\x00" mask: "\x00\xff" }
                      }
                      priority: 32
                    }
                  )pb"));

  RunPiEntityTest(info, "missing action",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554433
                      match {
                        field_id: 1
                        exact { value: "\xff\x22" }
                      }
                      match {
                        field_id: 2
                        exact { value: "\x10\x24\x32\x52" }
                      }
                    }
                  )pb"));

  RunPiEntityTest(info, "invalid action",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "action set in table with action",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "action in table with action set",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "missing action id",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "invalid action id",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "missing action params",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "duplicate action param id",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "invalid action param id",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "zero lpm prefix length",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554436
                      match {
                        field_id: 1
                        lpm { value: "\x10\x32\x41\x5" prefix_len: 0 }
                      }
                      action { action { action_id: 21257015 } }
                    }
                  )pb"));

  RunPiEntityTest(info, "zero ternary mask",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "zero priority",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "negative priority",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "absent priority",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "unexpected priority",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554436
                      match {
                        field_id: 1
                        lpm { value: "\x10\x32\x41\x00" prefix_len: 24 }
                      }
                      priority: 32
                      action { action { action_id: 21257015 } }
                    }
                  )pb"));

  RunPiEntityTest(info, "action set with negative weight",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "action set with invalid action",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "counter in a table with no counters",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));
  RunPiEntityTest(info, "action in a table with no actions defined",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "unsupported table used",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554447
                      match {
                        field_id: 1
                        exact { value: "\xff\x22" }
                      }
                      match {
                        field_id: 2
                        exact { value: "\x10\x24\x32\x52" }
                      }
                      match {
                        field_id: 3
                        exact { value: "\021\"3DUf" }
                      }
                    }
                  )pb"));

  RunPiEntityTest(info, "ternary table - unsupported action used",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554435
                      match {
                        field_id: 1
                        ternary { value: "\xd0" mask: "\x00\xff" }
                      }
                      action {
                        action {
                          action_id: 16777223
                          params { param_id: 1 value: "\xd0" }
                        }
                      }
                      priority: 32
                    }
                  )pb"));

  RunPiEntityTest(info, "ternary table - unsupported match field used",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunPiEntityTest(info, "meter counter data but missing meter config",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));
  RunPiEntityTest(info, "meter counter data in a table with no meters",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554440
                      match {
                        field_id: 1
                        lpm { value: "\020$2\000" prefix_len: 24 }
                      }
                      action { action { action_id: 16777220 } }
                      meter_config { cir: 123 cburst: 345 pir: 123 pburst: 345 }
                      counter_data { byte_count: 567 packet_count: 789 }
                      meter_counter_data {}
                    }
                  )pb"));
  RunPiEntityTest(info, "simple valid table translation",
                  gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                    table_entry {
                      table_id: 33554433
                      match {
                        field_id: 1
                        exact { value: "\377\"" }
                      }
                      match {
                        field_id: 2
                        exact { value: "\020$2R" }
                      }
                      action {
                        action {
                          action_id: 16777217
                          params { param_id: 1 value: "\010" }
                          params { param_id: 2 value: "\t" }
                        }
                      }
                    }
                  )pb"),
                  /*validity=*/INPUT_IS_VALID);
  RunPiMulticastTest(info);
  RunPiCloneSessionTest(info);
}  // NOLINT(readability/fn_size)

static void RunIrNoActionTableTests(const pdpi::IrP4Info& info) {
  // This function is defined separately and called from RunIrTests
  // since LINT complains if a function exceeds 500 lines.
  RunIrEntityTest(info, "action in a table with no actions defined",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                      }
                    }
                  )pb"));
}

static void RunIrTernaryTableTests(const pdpi::IrP4Info info) {
  RunIrEntityTest(info, "unsupported table used",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "unsupported_table"
                      matches {
                        name: "ipv4"
                        exact { ipv4: "10.10.10.10" }
                      }
                      matches {
                        name: "ipv6"
                        exact { ipv6: "::ff22" }
                      }
                      matches {
                        name: "mac"
                        exact { mac: "00:11:22:33:44:55" }
                      }
                    }
                  )pb"));
  RunIrEntityTest(info, "ternary table - unsupported action used",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "ternary_table"
                      matches {
                        name: "normal"
                        ternary { value { hex_str: "0x00" } }
                      }
                      action {
                        name: "unsupported_action"
                        params {
                          name: "normal"
                          value { hex_str: "0x012" }
                        }
                      }
                      priority: 32
                    }
                  )pb"));
  RunIrEntityTest(info, "ternary table - unsupported match field used",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "ternary_table"
                      matches {
                        name: "unsupported_field"
                        ternary { value { hex_str: "0x00" } }
                      }
                      priority: 32
                    }
                  )pb"));
}

static void RunIrMulticastTest(const pdpi::IrP4Info& info) {
  RunIrEntityTest(info, "multicast group entry with duplicate replica",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    packet_replication_engine_entry {
                      multicast_group_entry {
                        multicast_group_id: 7
                        replicas { port: "some_port" instance: 1 }
                        replicas { port: "some_port" instance: 1 }
                      }
                    }
                  )pb"));
  RunIrEntityTest(info, "valid multicast group entry",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    packet_replication_engine_entry {
                      multicast_group_entry {
                        multicast_group_id: 7
                        replicas { port: "some_port" instance: 1 }
                        replicas { port: "some_port" instance: 2 }
                        replicas { port: "some_other_port" instance: 1 }
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      .validity = INPUT_IS_VALID,
                  });
  RunIrEntityTest(info, "valid multicast group entry without explicit instance",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    packet_replication_engine_entry {
                      multicast_group_entry {
                        multicast_group_id: 7
                        replicas { port: "some_port" }
                        replicas { port: "some_other_port" }
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      .validity = INPUT_IS_VALID,
                  });
  RunIrEntityTest(
      info, "valid multicast group entry with backup replicas",
      gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 7
            replicas {
              port: "some_port"
              instance: 1
              backup_replicas { port: "some_other_port" instance: 2 }
              backup_replicas { port: "third_port" instance: 1 }
            }
            replicas {
              port: "some_other_port"
              instance: 1
              backup_replicas { port: "some_port" instance: 2 }
              backup_replicas { port: "third_port" instance: 2 }
            }
          }
        }
      )pb"),
      IrTestConfig{
          .validity = INPUT_IS_VALID,
          .test_ir_to_pd = false,
      });
  RunIrEntityTest(
      info,
      "multicast group entry with a backup replica that has the same port as "
      "the primary replica",
      gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 7
            replicas {
              port: "some_port"
              instance: 1
              backup_replicas { port: "some_port" instance: 2 }
              backup_replicas { port: "some_other_port" instance: 1 }
            }
          }
        }
      )pb"),
      IrTestConfig{
          .validity = INPUT_IS_INVALID,
          .test_ir_to_pd = false,
      });
  RunIrEntityTest(
      info,
      "multicast group entry with a backup replica that has the same port "
      "instance pair as another primary replica",
      gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 7
            replicas {
              port: "some_port"
              instance: 1
              backup_replicas { port: "some_other_port" instance: 2 }
            }
            replicas { port: "some_other_port" instance: 2 }
          }
        }
      )pb"),
      IrTestConfig{
          .validity = INPUT_IS_INVALID,
          .test_ir_to_pd = false,
      });
  RunIrEntityTest(
      info,
      "multicast group entry with a backup replica that has the same port "
      "instance pair as another backup replica",
      gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 7
            replicas {
              port: "some_port"
              instance: 1
              backup_replicas { port: "some_other_port" instance: 2 }
            }
            replicas {
              port: "third_port"
              instance: 3
              backup_replicas { port: "some_other_port" instance: 2 }
            }
          }
        }
      )pb"),
      IrTestConfig{
          .validity = INPUT_IS_INVALID,
          .test_ir_to_pd = false,
      });
}

static void RunIrCloneSessionTest(const pdpi::IrP4Info& info) {
  RunIrEntityTest(info, "clone session entry with duplicate replica",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    packet_replication_engine_entry {
                      clone_session_entry {
                        session_id: 7
                        replicas { port: "some_port" instance: 1 }
                        replicas { port: "some_port" instance: 1 }
                        class_of_service: 2
                        packet_length_bytes: 200
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      .validity = INPUT_IS_VALID,
                      .test_ir_to_pd = false,
                  });
  RunIrEntityTest(info, "valid clone session group entry",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    packet_replication_engine_entry {
                      clone_session_entry {
                        session_id: 7
                        replicas { port: "some_port" instance: 1 }
                        replicas { port: "some_port" instance: 2 }
                        replicas { port: "some_other_port" instance: 1 }
                        class_of_service: 2
                        packet_length_bytes: 200
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      .validity = INPUT_IS_VALID,
                      .test_ir_to_pd = false,
                  });
  RunIrEntityTest(info, "valid clone session entry without explicit instance",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    packet_replication_engine_entry {
                      clone_session_entry {
                        session_id: 7
                        replicas { port: "some_port" }
                        replicas { port: "some_other_port" }
                        class_of_service: 2
                        packet_length_bytes: 200
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      .validity = INPUT_IS_VALID,
                      .test_ir_to_pd = false,
                  });
}

static void RunPdMulticastTest(const pdpi::IrP4Info& info) {
  RunPdTableEntryTest(
      info, "multicast group entry with missing match field",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          action {
            replicate { replicas { port: "some_port" instance: "0x0001" } }
          }
        }
      )pb"),
      /*validity=*/INPUT_IS_INVALID);
  RunPdTableEntryTest(
      info, "multicast group entry with empty match field ",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match {}
          action {
            replicate { replicas { port: "some_port" instance: "0x0001" } }
          }
        }
      )pb"),
      /*validity=*/INPUT_IS_INVALID);
  RunPdTableEntryTest(
      info, "multicast group entry with invalid multicast_group_id format",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match { multicast_group_id: "not_a_hexstring" }
          action {
            replicate { replicas { port: "some_port" instance: "0x0001" } }
          }
        }
      )pb"),
      /*validity=*/INPUT_IS_INVALID);
  RunPdTableEntryTest(
      info, "multicast group entry with missing action",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry { match { multicast_group_id: "0x0007" } }
      )pb"),
      /*validity=*/INPUT_IS_INVALID);
  RunPdTableEntryTest(info, "multicast group entry with empty action",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        multicast_group_table_entry {
                          match { multicast_group_id: "0x0007" }
                          action {}
                        }
                      )pb"),
                      /*validity=*/INPUT_IS_INVALID);
  RunPdTableEntryTest(
      info, "multicast group entry with invalid instance format",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match { multicast_group_id: "0x0007" }
          action {
            replicate {
              replicas { port: "some_port" instance: "not_a_hexstring" }
            }
          }
        }
      )pb"),
      /*validity=*/INPUT_IS_INVALID);
  RunPdTableEntryTest(info, "multicast group entry with duplicate replica",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        multicast_group_table_entry {
                          match { multicast_group_id: "0x0007" }
                          action {
                            replicate {
                              replicas { port: "some_port" instance: "0x0001" }
                              replicas { port: "some_port" instance: "0x0001" }
                            }
                          }
                        }
                      )pb"),
                      /*validity=*/INPUT_IS_INVALID);
  RunPdTableEntryTest(
      info, "valid multicast group entry",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match { multicast_group_id: "0x0007" }
          action {
            replicate {
              replicas { port: "some_port" instance: "0x0001" }
              replicas { port: "some_port" instance: "0x0002" }
              replicas { port: "some_other_port" instance: "0x0001" }
            }
          }
        }
      )pb"),
      /*validity=*/INPUT_IS_VALID);
  RunPdTableEntryTest(
      info, "valid multicast group entry with instance set to 0",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match { multicast_group_id: "0x0007" }
          action {
            replicate {
              replicas { port: "some_port" instance: "0x0000" }
              replicas { port: "some_other_port" instance: "0x0000" }
            }
          }
        }
      )pb"),
      /*validity=*/INPUT_IS_VALID);
  RunPdTableEntryTest(info,
                      "valid multicast group entry with empty replicate action",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        multicast_group_table_entry {
                          match { multicast_group_id: "0x0007" }
                          action { replicate {} }
                        }
                      )pb"),
                      /*validity=*/INPUT_IS_VALID);
  RunPdTableEntryTest(
      info, "valid multicast group entry with metadata",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match { multicast_group_id: "0x0001" }
          action {
            replicate { replicas { port: "some_port" instance: "0x0000" } }
          }
          metadata: "my_metadata"
        }
      )pb"),
      /*validity=*/INPUT_IS_VALID);
}

static void RunIrMeterCounterTableEntryTests(const pdpi::IrP4Info& info) {
  RunIrEntityTest(info, "meter counter data in a table with no counters",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"),
                  IrTestConfig{
                      // Not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });
  RunIrEntityTest(info, "meter counter data but missing meter config",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"),
                  IrTestConfig{
                      // Not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });
}

static void RunIrTests(const pdpi::IrP4Info info) {
  RunIrEntityTest(info, "empty IR",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb()pb"));

  RunIrEntityTest(info, "empty table IR",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {}
                  )pb"));

  RunIrEntityTest(info, "invalid table name",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry { table_name: "invalid" }
                  )pb"));

  RunIrEntityTest(info, "missing matches",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry { table_name: "id_test_table" }
                  )pb"),
                  IrTestConfig{
                      // Missing matches are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "invalid match type - expect exact",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "id_test_table"
                      matches {
                        name: "ipv6"
                        lpm {
                          value { ipv6: "::ff22" }
                          prefix_length: 96
                        }
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      // Match types are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "invalid match type - expect optional",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "optional_table"
                      matches {
                        name: "ipv6"
                        lpm {
                          value { ipv6: "::ff22" }
                          prefix_length: 96
                        }
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      // Match types are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "invalid match type - expect lpm",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "lpm2_table"
                      matches {
                        name: "ipv6"
                        ternary {
                          value { ipv6: "::ff22" }
                          mask { ipv6: "::00d3:5412" }
                        }
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      // Match types are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "invalid match type - expect ternary",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "ternary_table"
                      matches {
                        name: "ipv6"
                        exact { ipv6: "::ff22" }
                      }
                      priority: 32
                    }
                  )pb"),
                  IrTestConfig{
                      // Match types are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(
      info, "invalid value - address not in bounds for upper 64 bits of ipv6",
      gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
        table_entry {
          table_name: "ternary_table"
          matches {
            name: "ipv6_upper_64_bits"
            ternary {
              value { ipv6: "::ff22" }
              mask { ipv6: "::ffff" }
            }
          }
          priority: 32
        }
      )pb"),
      IrTestConfig{
          // Bitwidths are not currently checked for IR->PD.
          .test_ir_to_pd = false,
      });

  RunIrEntityTest(
      info, "invalid value - address not in bounds for upper 63 bits of ipv6",
      gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
        table_entry {
          table_name: "ternary_table"
          matches {
            name: "ipv6_upper_63_bits"
            ternary {
              value { ipv6: "ff::" }
              mask { ipv6: "ffff:ffff:ffff:ffff::" }
            }
          }
          priority: 32
        }
      )pb"),
      IrTestConfig{
          // Bitwidths are not currently checked for IR->PD.
          .test_ir_to_pd = false,
      });

  RunIrEntityTest(
      info, "invalid match field name",
      gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
        table_entry {
          table_name: "id_test_table"
          matches {
            name: "invalid"
            exact { ipv6: "::ff22" }
          }
        }
      )pb"),
      IrTestConfig{
          // Invalid match field names are not currently checked for IR->PD.
          .test_ir_to_pd = false,
      });

  RunIrEntityTest(info, "invalid IR value",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "id_test_table"
                      matches {
                        name: "ipv4"
                        exact { ipv6: "::ff22" }
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      // Formats are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "invalid prefix length",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "lpm1_table"
                      matches {
                        name: "ipv4"
                        lpm {
                          value { ipv4: "10.32.14.2" }
                          prefix_length: 40
                        }
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      // Formats are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "duplicate match field name",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "id_test_table"
                      matches {
                        name: "ipv6"
                        exact { ipv6: "::ff22" }
                      }
                      matches {
                        name: "ipv6"
                        exact { ipv4: "10.24.32.52" }
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      // Duplicates are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "lpm value - masked bits set",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "lpm1_table"
                      matches {
                        name: "ipv4"
                        lpm {
                          value { ipv4: "10.43.23.12" }
                          prefix_length: 24
                        }
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      // Formats are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "ternary value too long",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "ternary_table"
                      matches {
                        name: "normal"
                        ternary {
                          value { hex_str: "0x4212" }
                          mask { hex_str: "0x00ff" }
                        }
                      }
                      priority: 32
                    }
                  )pb"),
                  IrTestConfig{
                      // Formats are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "ternary value and mask too long",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "ternary_table"
                      matches {
                        name: "normal"
                        ternary {
                          value { hex_str: "0x4212" }
                          mask { hex_str: "0x0fff" }
                        }
                      }
                      priority: 32
                    }
                  )pb"),
                  IrTestConfig{
                      // Formats are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "ternary value - masked bits set",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "ternary_table"
                      matches {
                        name: "ipv6"
                        ternary {
                          value { ipv6: "::0100" }
                          mask { ipv6: "::00ff" }
                        }
                      }
                      priority: 32
                    }
                  )pb"),
                  IrTestConfig{
                      // Formats are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "Invalid match field format",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "ternary_table"
                      matches {
                        name: "ipv6"
                        ternary {
                          value { ipv4: "127.0.0.0" }
                          mask { ipv4: "127.0.0.0" }
                        }
                      }
                      priority: 32
                    }
                  )pb"),
                  IrTestConfig{
                      // Formats are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "missing action",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "id_test_table"
                      matches {
                        name: "ipv6"
                        exact { ipv6: "::ff22" }
                      }
                      matches {
                        name: "ipv4"
                        exact { ipv4: "10.24.32.52" }
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      // Missing actions are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "missing action name",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunIrEntityTest(info, "invalid action name",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunIrEntityTest(info, "missing action params",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"),
                  IrTestConfig{
                      // Action parameters are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "duplicate action param name",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"),
                  IrTestConfig{
                      // Action parameters are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(
      info, "bad action param format",
      gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
        table_entry {
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
        }
      )pb"),
      IrTestConfig{
          // Action parameter formats are not currently checked for IR->PD.
          .test_ir_to_pd = false,
      });

  RunIrEntityTest(info, "invalid action param name",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunIrEntityTest(info, "action set in table with action",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"),
                  IrTestConfig{
                      // Actions are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "action in table with action set",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"),
                  IrTestConfig{
                      // Actions are not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "zero lpm prefix length",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "lpm1_table"
                      matches {
                        name: "ipv4"
                        lpm {
                          value { ipv4: "10.32.41.5" }
                          prefix_length: 0
                        }
                      }
                      action { name: "NoAction" }
                    }
                  )pb"),
                  IrTestConfig{
                      // Not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "zero ternary mask",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunIrEntityTest(info, "empty bytestring in match field",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "optional_table"
                      matches {
                        name: "str"
                        optional { value { str: "" } }
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
                    }
                  )pb"),
                  IrTestConfig{
                      // Not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "empty bytestring in action parameter",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "id_test_table"
                      matches {
                        name: "ipv6"
                        exact { ipv6: "::ff22" }
                      }
                      matches {
                        name: "ipv4"
                        exact { ipv4: "16.36.50.82" }
                      }
                      action {
                        name: "do_thing_2"
                        params {
                          name: "normal"
                          value { hex_str: "0x054" }
                        }
                        params {
                          name: "ipv4"
                          value { ipv4: "10.43.12.5" }
                        }
                        params {
                          name: "ipv6"
                          value { ipv6: "3242::fee2" }
                        }
                        params {
                          name: "mac"
                          value { mac: "00:11:22:33:44:55" }
                        }
                        params {
                          name: "str"
                          value { str: "" }
                        }
                      }
                    }
                  )pb"),
                  IrTestConfig{
                      // Not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "zero priority",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunIrEntityTest(info, "negative priority",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunIrEntityTest(info, "absent priority",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunIrEntityTest(info, "unexpected priority",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunIrEntityTest(info, "action set with negative weight",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"),
                  IrTestConfig{
                      // Not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });

  RunIrEntityTest(info, "action set with invalid action",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"));

  RunIrEntityTest(info, "counter in a table with no counters",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
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
                    }
                  )pb"),
                  IrTestConfig{
                      // Not currently checked for IR->PD.
                      .test_ir_to_pd = false,
                  });
  RunIrNoActionTableTests(info);
  RunIrTernaryTableTests(info);
  RunIrMeterCounterTableEntryTests(info);
  // Example test for INPUT_IS_VALID setting.
  RunIrEntityTest(info, "valid table translation with INPUT_IS_VALID set",
                  gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                    table_entry {
                      table_name: "id_test_table"
                      matches {
                        name: "ipv6"
                        exact { ipv6: "::ff22" }
                      }
                      matches {
                        name: "ipv4"
                        exact { ipv4: "16.36.50.82" }
                      }
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
                    }
                  )pb"),
                  IrTestConfig{
                      .validity = INPUT_IS_VALID,
                  });
  RunIrMulticastTest(info);
  RunIrCloneSessionTest(info);
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

// Take the `p4info` argument in as a copy since we will be updating it for the
// tests.
static absl::Status RunPdTestWithMeterAndCounterDataRemoved(
    p4::config::v1::P4Info p4info) {
  // Remove all direct counters and meters from the P4 program.
  p4info.clear_direct_meters();
  p4info.clear_direct_counters();
  for (auto& table : *p4info.mutable_tables()) {
    table.clear_direct_resource_ids();
  }
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::CreateIrP4Info(p4info));

  RunPdTableEntryTest(
      ir_p4info, "table entry with unallowed meter config",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          meter_config { bytes_per_second: 123 burst_bytes: 345 }
        }
      )pb"),
      INPUT_IS_INVALID);
  RunPdTableEntryTest(
      ir_p4info, "table entry with unallowed counter data",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          counter_data { byte_count: 567 packet_count: 789 }
        }
      )pb"),
      INPUT_IS_INVALID);
  RunPdTableEntryTest(
      ir_p4info, "table entry with unallowed meter config and counter data",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        count_and_meter_table_entry {
          match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
          action { count_and_meter {} }
          meter_config { bytes_per_second: 123 burst_bytes: 345 }
          counter_data { byte_count: 567 packet_count: 789 }
        }
      )pb"),
      INPUT_IS_INVALID);
  return absl::OkStatus();
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

  RunPdTableEntryTest(info, "value with empty string for Format::STRING",
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
  RunPdMulticastTest(info);
}

static void RunPdTestsOnlyKey(const pdpi::IrP4Info info) {
  RunPdTableEntryTest(info, "missing matches with key_only=true",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        id_test_table_entry {}
                      )pb"),
                      INPUT_IS_INVALID,
                      pdpi::TranslationOptions{.key_only = true});

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
      INPUT_IS_INVALID, pdpi::TranslationOptions{.key_only = true});

  RunPdTableEntryTest(
      info, "unsupported table used",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        unsupported_table_entry {
          match { ipv4: "10.10.10.10" ipv6: "::ff22" mac: "11:22:33:44:55:66" }
        }
      )pb"),
      INPUT_IS_INVALID);
  RunPdTableEntryTest(
      info, "unsupported table used",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        unsupported_table_entry {
          match { ipv4: "10.10.10.10" ipv6: "::ff22" mac: "11:22:33:44:55:66" }
        }
      )pb"),
      INPUT_IS_VALID, pdpi::TranslationOptions{.allow_unsupported = true});

  RunPdTableEntryTest(info, "ternary table - unsupported action used",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        ternary_table_entry {
                          match { normal { value: "0x052" mask: "0x273" } }
                          priority: 32
                          action { unsupported_action { normal: "0x054" } }
                        }
                      )pb"),
                      INPUT_IS_INVALID);
  RunPdTableEntryTest(info, "ternary table - unsupported action used",
                      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
                        ternary_table_entry {
                          match { normal { value: "0x052" mask: "0x273" } }
                          priority: 32
                          action { unsupported_action { normal: "0x054" } }
                        }
                      )pb"),
                      INPUT_IS_VALID,
                      pdpi::TranslationOptions{.allow_unsupported = true});

  RunPdTableEntryTest(
      info, "ternary table - unsupported match field used",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match { unsupported_field { value: "0x1" mask: "0x1" } }
          priority: 32
          action { do_thing_3 { arg1: "0x12345678" arg2: "0x87654321" } }
        }
      )pb"),
      INPUT_IS_INVALID);
  RunPdTableEntryTest(
      info, "ternary table - unsupported match field used",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match { unsupported_field { value: "0x1" mask: "0x1" } }
          priority: 32
          action { do_thing_3 { arg1: "0x12345678" arg2: "0x87654321" } }
        }
      )pb"),
      INPUT_IS_VALID, pdpi::TranslationOptions{.allow_unsupported = true});

  RunPdTableEntryTest(
      info, "ipv4 LPM table with key_only=true",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        lpm1_table_entry {
          match { ipv4 { value: "10.43.12.0" prefix_length: 24 } }
          action { NoAction {} }
        }
      )pb"),
      INPUT_IS_VALID, pdpi::TranslationOptions{.key_only = true});

  RunPdTableEntryTest(
      info, "ternary match with key_only=true",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        ternary_table_entry {
          match { normal { value: "0x052" mask: "0x273" } }
          priority: 32
          action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
        }
      )pb"),
      INPUT_IS_VALID, pdpi::TranslationOptions{.key_only = true});
  RunPdTableEntryTest(
      info, "multicast group entry with key_only=true",
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match { multicast_group_id: "0x0007" }
          action {
            replicate {
              replicas { port: "some_port" instance: "0x0001" }
              replicas { port: "some_port" instance: "0x0002" }
              replicas { port: "some_other_port" instance: "0x0001" }
            }
          }
        }
      )pb"),
      /*validity=*/INPUT_IS_VALID, pdpi::TranslationOptions{.key_only = true});
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

  absl::Status meter_and_counter_tests =
      RunPdTestWithMeterAndCounterDataRemoved(p4info);
  if (!meter_and_counter_tests.ok()) {
    std::cerr << meter_and_counter_tests.ToString() << std::endl;
    return 1;
  }

  return 0;
}

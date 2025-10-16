// Copyright 2021 Google LLC
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
#include "p4rt_app/p4runtime/ir_translation.h"

#include "absl/strings/string_view.h"
#include "boost/bimap.hpp"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/queue_translator.h"
#include "p4rt_app/utils/ir_builder.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace {

using ::google::protobuf::TextFormat;
using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::HasSubstr;

// Helper method so all tests use the same IrP4Info.
const pdpi::IrP4Info& GetIrP4Info() {
  return sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
}

const QueueTranslator& EmptyCpuQueueTranslator() {
  static const auto* const kTranslator = QueueTranslator::Empty().release();
  return *kTranslator;
}

TEST(PortTranslationTest, TranslatePort) {
  boost::bimap<std::string, std::string> map;
  map.insert({"key0", "val0"});
  map.insert({"key1", "val1"});
  EXPECT_THAT(TranslatePort(TranslationDirection::kForController, map, "key0"),
              IsOkAndHolds("val0"));
  EXPECT_THAT(TranslatePort(TranslationDirection::kForOrchAgent, map, "val0"),
              IsOkAndHolds("key0"));
}

TEST(PortTranslationTest, TranslatePortFailsWithMissingKey) {
  boost::bimap<std::string, std::string> map;
  map.insert({"key0", "val0"});
  map.insert({"key1", "val1"});
  EXPECT_THAT(TranslatePort(TranslationDirection::kForController, map, "key2"),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(TranslatePort(TranslationDirection::kForOrchAgent, map, "val2"),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(PortIdTranslationTest, ActionParameterUpdatedToPortName) {
  boost::bimap<std::string, std::string> port_translation_map;
  port_translation_map.insert({"Ethernet0", "1"});
  port_translation_map.insert({"Ethernet4", "2"});

  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        table_name: "router_interface_table"
        action {
          name: "set_port_and_src_mac"
          params {
            name: "port"
            value { str: "1" }
          }
        })pb",
      &table_entry));
  ASSERT_OK(TranslateTableEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = GetIrP4Info(),
          .translate_port_ids = true,
          .port_map = port_translation_map,
          .cpu_queue_translator = EmptyCpuQueueTranslator(),
      },
      table_entry));
  ASSERT_EQ(table_entry.action().params_size(), 1);
  EXPECT_EQ(table_entry.action().params(0).value().str(), "Ethernet0");
}

TEST(PortIdTranslationTest, WatchPortUpdatedToPortName) {
  boost::bimap<std::string, std::string> port_translation_map;
  port_translation_map.insert({"Ethernet0", "1"});
  port_translation_map.insert({"Ethernet4", "2"});

  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(
                                            table_name: "wcmp_group_table"
                                            action_set {
                                              actions {
                                                action {
                                                  name: "set_nexthop_id"
                                                  params {
                                                    name: "nexthop_id"
                                                    value { str: "1" }
                                                  }
                                                }
                                                weight: 1
                                                watch_port: "2"
                                              }
                                            })pb",
                                          &table_entry));
  ASSERT_OK(TranslateTableEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = GetIrP4Info(),
          .translate_port_ids = true,
          .port_map = port_translation_map,
          .cpu_queue_translator = EmptyCpuQueueTranslator(),
      },
      table_entry));

  // Expect the watch_port to change.
  ASSERT_EQ(table_entry.action_set().actions_size(), 1);
  EXPECT_EQ(table_entry.action_set().actions(0).watch_port(), "Ethernet4");
}

TEST(PortIdTranslationTest, ExactMatchFieldUpdatedToPortName) {
  boost::bimap<std::string, std::string> port_translation_map;
  port_translation_map.insert({"Ethernet0", "1"});
  port_translation_map.insert({"Ethernet4", "2"});

  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        table_name: "l3_admit_table"
        matches {
          name: "in_port"
          exact { str: "2" }
        })pb",
      &table_entry));

  ASSERT_OK(TranslateTableEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = GetIrP4Info(),
          .translate_port_ids = true,
          .port_map = port_translation_map,
          .cpu_queue_translator = EmptyCpuQueueTranslator(),
      },
      table_entry));
  ASSERT_EQ(table_entry.matches_size(), 1);
  EXPECT_EQ(table_entry.matches(0).exact().str(), "Ethernet4");
}

TEST(PortIdTranslationTest, OptionalMatchFieldUpdatedToPortName) {
  boost::bimap<std::string, std::string> port_translation_map;
  port_translation_map.insert({"Ethernet0", "1"});
  port_translation_map.insert({"Ethernet4", "2"});

  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(
                                            table_name: "acl_pre_ingress_table"
                                            matches {
                                              name: "in_port"
                                              optional { value { str: "2" } }
                                            })pb",
                                          &table_entry));
  ASSERT_OK(TranslateTableEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = GetIrP4Info(),
          .translate_port_ids = true,
          .port_map = port_translation_map,
          .cpu_queue_translator = EmptyCpuQueueTranslator(),
      },
      table_entry));
  ASSERT_EQ(table_entry.matches_size(), 1);
  EXPECT_EQ(table_entry.matches(0).optional().value().str(), "Ethernet4");
}

TEST(PortNamePassthroughTest, ActionParametersIgnoresPortName) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        table_name: "router_interface_table"
        action {
          name: "set_port_and_src_mac"
          params {
            name: "port"
            value { str: "Ethernet0" }
          }
        })pb",
      &table_entry));

  ASSERT_OK(TranslateTableEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = GetIrP4Info(),
          .translate_port_ids = false,
          .port_map = {},
          .cpu_queue_translator = EmptyCpuQueueTranslator(),
      },
      table_entry));
  ASSERT_EQ(table_entry.action().params_size(), 1);
  EXPECT_EQ(table_entry.action().params(0).value().str(), "Ethernet0");
}

TEST(PortNamePassthroughTest, WatchPortIgnoresPortName) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(
                                            table_name: "wcmp_group_table"
                                            action_set {
                                              actions {
                                                action {
                                                  name: "set_nexthop_id"
                                                  params {
                                                    name: "nexthop_id"
                                                    value { str: "Ethernet0" }
                                                  }
                                                }
                                                weight: 1
                                                watch_port: "Ethernet4"
                                              }
                                            })pb",
                                          &table_entry));
  ASSERT_OK(TranslateTableEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = GetIrP4Info(),
          .translate_port_ids = false,
          .port_map = {},
          .cpu_queue_translator = EmptyCpuQueueTranslator(),
      },
      table_entry));

  // Expect the watch_port to change.
  ASSERT_EQ(table_entry.action_set().actions_size(), 1);
  EXPECT_EQ(table_entry.action_set().actions(0).watch_port(), "Ethernet4");
}

TEST(PortNamePassthroughTest, ExactMatchFieldIgnoresPortName) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        table_name: "l3_admit_table"
        matches {
          name: "in_port"
          exact { str: "Ethernet4" }
        })pb",
      &table_entry));

  ASSERT_OK(TranslateTableEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = GetIrP4Info(),
          .translate_port_ids = false,
          .port_map = {},
          .cpu_queue_translator = EmptyCpuQueueTranslator(),
      },
      table_entry));
  ASSERT_EQ(table_entry.matches_size(), 1);
  EXPECT_EQ(table_entry.matches(0).exact().str(), "Ethernet4");
}

TEST(PortNamePassthroughTest, OptionalMatchFieldIgnoresPortName) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
                                    table_name: "acl_pre_ingress_table"
                                    matches {
                                      name: "in_port"
                                      optional { value { str: "Ethernet4" } }
                                    })pb",
                                  &table_entry));
  ASSERT_OK(TranslateTableEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = GetIrP4Info(),
          .translate_port_ids = false,
          .port_map = {},
          .cpu_queue_translator = EmptyCpuQueueTranslator(),
      },
      table_entry));
  ASSERT_EQ(table_entry.matches_size(), 1);
  EXPECT_EQ(table_entry.matches(0).optional().value().str(), "Ethernet4");
}

TEST(IrTranslationTest, InvalidTableNameFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(table_name: "sample_name"
                                               action {
                                                 name: "sample_action"
                                                 params {
                                                   name: "sample_param"
                                                   value { str: "1" }
                                                 }
                                               })pb",
                                          &table_entry));

  boost::bimap<std::string, std::string> port_translation_map;
  EXPECT_THAT(TranslateTableEntry(
                  TranslateTableEntryOptions{
                      .direction = TranslationDirection::kForOrchAgent,
                      .ir_p4_info = GetIrP4Info(),
                      .translate_port_ids = true,
                      .port_map = port_translation_map,
                      .cpu_queue_translator = EmptyCpuQueueTranslator(),
                  },
                  table_entry),
              StatusIs(absl::StatusCode::kInternal, HasSubstr("sample_name")));
}

TEST(IrTranslationTest, InvalidMatchFieldNameFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        table_name: "l3_admit_table"
        matches {
          name: "in_port"
          ternary {
            value { str: "2" }
            mask { str: "2" }
          }
        })pb",
      &table_entry));

  boost::bimap<std::string, std::string> port_translation_map;
  EXPECT_THAT(TranslateTableEntry(
                  TranslateTableEntryOptions{
                      .direction = TranslationDirection::kForOrchAgent,
                      .ir_p4_info = GetIrP4Info(),
                      .translate_port_ids = true,
                      .port_map = port_translation_map,
                      .cpu_queue_translator = EmptyCpuQueueTranslator(),
                  },
                  table_entry),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(IrTranslationTest, InvalidMatchFieldTypeFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        table_name: "l3_admit_table"
        matches {
          name: "sample_field"
          exact { str: "2" }
        })pb",
      &table_entry));

  boost::bimap<std::string, std::string> port_translation_map;
  EXPECT_THAT(TranslateTableEntry(
                  TranslateTableEntryOptions{
                      .direction = TranslationDirection::kForOrchAgent,
                      .ir_p4_info = GetIrP4Info(),
                      .translate_port_ids = true,
                      .port_map = port_translation_map,
                      .cpu_queue_translator = EmptyCpuQueueTranslator(),
                  },
                  table_entry),
              StatusIs(absl::StatusCode::kInternal, HasSubstr("sample_field")));
}

TEST(IrTranslationTest, InvalidActionNameFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        table_name: "router_interface_table"
        action {
          name: "some_action"
          params {
            name: "port"
            value { str: "1" }
          }
        })pb",
      &table_entry));

  boost::bimap<std::string, std::string> port_translation_map;
  EXPECT_THAT(TranslateTableEntry(
                  TranslateTableEntryOptions{
                      .direction = TranslationDirection::kForOrchAgent,
                      .ir_p4_info = GetIrP4Info(),
                      .translate_port_ids = true,
                      .port_map = port_translation_map,
                      .cpu_queue_translator = EmptyCpuQueueTranslator(),
                  },
                  table_entry),
              StatusIs(absl::StatusCode::kInternal, HasSubstr("some_action")));
}

TEST(IrTranslationTest, InvalidActionParameterNameFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        table_name: "router_interface_table"
        action {
          name: "set_port_and_src_mac"
          params {
            name: "some_param"
            value { str: "1" }
          }
        })pb",
      &table_entry));

  boost::bimap<std::string, std::string> port_translation_map;
  EXPECT_THAT(TranslateTableEntry(
                  TranslateTableEntryOptions{
                      .direction = TranslationDirection::kForOrchAgent,
                      .ir_p4_info = GetIrP4Info(),
                      .translate_port_ids = true,
                      .port_map = port_translation_map,
                      .cpu_queue_translator = EmptyCpuQueueTranslator(),
                  },
                  table_entry),
              StatusIs(absl::StatusCode::kInternal, HasSubstr("some_param")));
}

TEST(IrTranslationTest, ActionParametersWithUnsupportedFormatFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        table_name: "router_interface_table"
        action {
          name: "set_port_and_src_mac"
          params {
            name: "port"
            value { hex_str: "1" }
          }
        })pb",
      &table_entry));

  boost::bimap<std::string, std::string> port_translation_map;
  EXPECT_THAT(TranslateTableEntry(
                  TranslateTableEntryOptions{
                      .direction = TranslationDirection::kForController,
                      .ir_p4_info = GetIrP4Info(),
                      .translate_port_ids = true,
                      .port_map = port_translation_map,
                      .cpu_queue_translator = EmptyCpuQueueTranslator(),
                  },
                  table_entry),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(P4RuntimeTweaksP4InfoTest, ForOrchAgentSetsCompositeUdfFormatToString) {
  const std::string match_field_proto_string =
      R"pb(id: 123
           name: "match_field_name"
           annotations: "@composite_field(@sai_udf(base=SAI_UDF_BASE_L3, offset=2, length=2), @sai_udf(base=SAI_UDF_BASE_L3, offset=4, length=2))")pb";

  pdpi::IrTableDefinition ir_table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" id: 1)pb")
          .match_field(match_field_proto_string, pdpi::IPV4)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action_name")pb"))
          .size(512)();

  pdpi::IrP4Info ir_p4_info;
  (*ir_p4_info.mutable_tables_by_id())[1] = ir_table;
  (*ir_p4_info.mutable_tables_by_name())["Table"] = ir_table;

  pdpi::IrTableDefinition ir_table_with_string_format =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" id: 1)pb")
          .match_field(match_field_proto_string, pdpi::HEX_STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action_name")pb"))
          .size(512)();

  TranslateIrP4InfoForOrchAgent(ir_p4_info);
  EXPECT_THAT(ir_p4_info.tables_by_id().at(1),
              EqualsProto(ir_table_with_string_format));
  EXPECT_THAT(ir_p4_info.tables_by_name().at("Table"),
              EqualsProto(ir_table_with_string_format));
}

// We're only testing non-udf & all-udf. Partial-udf isn't supported, so it does
// not need to be tested.
TEST(P4RuntimeTweaksP4InfoTest, ForOrchAgentIgnoresCompositeNonUdfFields) {
  const std::string match_field_proto_string =
      R"pb(id: 123
           name: "match_field_name"
           annotations: "@composite_field(@sai_field(SAI_FIELD1), @sai_field(SAI_FIELD2))")pb";

  pdpi::IrTableDefinition ir_table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" id: 1)pb")
          .match_field(match_field_proto_string, pdpi::IPV4)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action_name")pb"))
          .size(512)();

  pdpi::IrP4Info ir_p4_info;
  (*ir_p4_info.mutable_tables_by_id())[1] = ir_table;
  (*ir_p4_info.mutable_tables_by_name())["Table"] = ir_table;

  pdpi::IrP4Info unchanged_ir_p4_info = ir_p4_info;
  TranslateIrP4InfoForOrchAgent(ir_p4_info);
  EXPECT_THAT(ir_p4_info, EqualsProto(unchanged_ir_p4_info));
}

// TODO: Remove tests below when P4Info uses 64-bit IPv6 ACL match
// fields.
TEST(Convert64BitIpv6AclMatchFieldsTo128BitTest, PadsSmallAddresses) {
  pdpi::IrTableEntry ir_table_entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        table_name: "table"
        matches {
          name: "ipv6_src"
          ternary {
            value { ipv6: "::aaaa:aaaa:aaaa:aaaa" }
            mask { ipv6: "::ffff:ffff:ffff:ffff" }
          }
        }
        matches {
          name: "ipv6_dst"
          ternary {
            value { ipv6: "::bbbb:bbbb:bbbb:bbbb" }
            mask { ipv6: "::ffff:ffff:ffff:ffff" }
          }
        }
      )pb",
      &ir_table_entry));
  Convert64BitIpv6AclMatchFieldsTo128Bit(ir_table_entry);
  EXPECT_THAT(ir_table_entry, EqualsProto(
                                  R"pb(
                                    table_name: "table"
                                    matches {
                                      name: "ipv6_src"
                                      ternary {
                                        value { ipv6: "aaaa:aaaa:aaaa:aaaa::" }
                                        mask { ipv6: "ffff:ffff:ffff:ffff::" }
                                      }
                                    }
                                    matches {
                                      name: "ipv6_dst"
                                      ternary {
                                        value { ipv6: "bbbb:bbbb:bbbb:bbbb::" }
                                        mask { ipv6: "ffff:ffff:ffff:ffff::" }
                                      }
                                    }
                                  )pb"));
}

TEST(Convert64BitIpv6AclMatchFieldsTo128BitTest, KeepsLargeAddresses) {
  pdpi::IrTableEntry ir_table_entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        table_name: "table"
        matches {
          name: "ipv6_src"
          ternary {
            value { ipv6: "1::aaaa:aaaa:aaaa:aaaa" }
            mask { ipv6: "1::ffff:ffff:ffff:ffff" }
          }
        }
        matches {
          name: "ipv6_dst"
          ternary {
            value { ipv6: "1::bbbb:bbbb:bbbb:bbbb" }
            mask { ipv6: "1::ffff:ffff:ffff:ffff" }
          }
        }
      )pb",
      &ir_table_entry));

  pdpi::IrTableEntry original_ir_table_entry = ir_table_entry;
  Convert64BitIpv6AclMatchFieldsTo128Bit(ir_table_entry);
  EXPECT_THAT(ir_table_entry, EqualsProto(original_ir_table_entry));
}

TEST(Convert64BitIpv6AclMatchFieldsTo128BitTest, KeepsNonTernaryAddresses) {
  pdpi::IrTableEntry ir_table_entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        table_name: "table"
        matches {
          name: "ipv6_src"
          lpm { value { ipv6: "::ffff:ffff:ffff:ffff" } }
        }
        matches {
          name: "ipv6_dst"
          optional { value { ipv6: "::bbbb:bbbb:bbbb:bbbb" } }
        }
      )pb",
      &ir_table_entry));

  pdpi::IrTableEntry original_ir_table_entry = ir_table_entry;
  Convert64BitIpv6AclMatchFieldsTo128Bit(ir_table_entry);
  EXPECT_THAT(ir_table_entry, EqualsProto(original_ir_table_entry));
}

TEST(TranslateTableEntry, TranslatesCpuQueueNameToAppDbId) {
  pdpi::IrEntity queue_name_table_entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        table_entry {
          table_name: "acl_ingress_table"
          matches {
            name: "is_ip"
            optional { value { hex_str: "0x1" } }
          }
          action {
            name: "acl_trap"
            params {
              name: "qos_queue"
              value { str: "queue15" }
            }
          }
        }
      )pb",
      &queue_name_table_entry));

  // Translate the table entry using the cpu queue translator.
  ASSERT_OK_AND_ASSIGN(auto cpu_queue_translator,
                       QueueTranslator::Create({{"queue15", "15"}}));
  EXPECT_OK(UpdateIrEntityForOrchAgent(
      queue_name_table_entry, GetIrP4Info(), /*translate_port_ids=*/false,
      /*port_translation_map=*/{}, *cpu_queue_translator));

  // Expect that everything is the same except the cpu queue name has been
  // translated.
  pdpi::IrEntity queue_id_table_entry = queue_name_table_entry;
  queue_id_table_entry.mutable_table_entry()
      ->mutable_action()
      ->mutable_params(0)
      ->mutable_value()
      ->set_str("0xf");
  EXPECT_THAT(queue_name_table_entry, EqualsProto(queue_id_table_entry));
}

TEST(TranslateTableEntry, IgnoresUnknownCpuQueueNameToAppDbIdTranslation) {
  pdpi::IrEntity ir_table_entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        table_entry {
          table_name: "acl_ingress_table"
          matches {
            name: "is_ip"
            optional { value { hex_str: "0x1" } }
          }
          action {
            name: "acl_trap"
            params {
              name: "qos_queue"
              value { str: "queue2" }
            }
          }
        }
      )pb",
      &ir_table_entry));
  const pdpi::IrEntity original_table_entry = ir_table_entry;

  // Add a different queue.
  ASSERT_OK_AND_ASSIGN(auto cpu_queue_translator,
                       QueueTranslator::Create({{"queue1", "1"}}));

  EXPECT_OK(UpdateIrEntityForOrchAgent(
      ir_table_entry, GetIrP4Info(), /*translate_port_ids=*/false,
      /*port_translation_map=*/{}, *cpu_queue_translator));
  EXPECT_THAT(ir_table_entry, EqualsProto(original_table_entry));
}

TEST(TranslateTableEntry, TranslatesAppDbCpuQueueIdToName) {
  pdpi::IrTableEntry ir_table_entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        table_name: "acl_ingress_table"
        matches {
          name: "is_ip"
          optional { value { hex_str: "0x1" } }
        }
        action {
          name: "acl_trap"
          params {
            name: "qos_queue"
            value { str: "0xa" }
          }
        }
      )pb",
      &ir_table_entry));
  pdpi::IrTableEntry queue_name_table_entry = ir_table_entry;
  queue_name_table_entry.mutable_action()
      ->mutable_params(0)
      ->mutable_value()
      ->set_str("queue10");

  ASSERT_OK_AND_ASSIGN(auto cpu_queue_translator,
                       QueueTranslator::Create({{"queue10", "10"}}));

  TranslateTableEntryOptions options = {
      .direction = TranslationDirection::kForController,
      .ir_p4_info = GetIrP4Info(),
      .translate_port_ids = false,
      .port_map = {},
      .cpu_queue_translator = *cpu_queue_translator,
  };

  EXPECT_OK(TranslateTableEntry(options, ir_table_entry));
  EXPECT_THAT(ir_table_entry, EqualsProto(queue_name_table_entry));
}

TEST(TranslateTableEntry, IgnoresUnknownAppDbCpuQueueIdToNameTranslation) {
  pdpi::IrTableEntry ir_table_entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        table_name: "acl_ingress_table"
        matches {
          name: "is_ip"
          optional { value { hex_str: "0x1" } }
        }
        action {
          name: "acl_trap"
          params {
            name: "qos_queue"
            value { str: "0x3" }
          }
        }
      )pb",
      &ir_table_entry));
  const pdpi::IrTableEntry original_table_entry = ir_table_entry;

  // Set up a different queue.
  ASSERT_OK_AND_ASSIGN(auto cpu_queue_translator,
                       QueueTranslator::Create({{"queue2", "2"}}));

  TranslateTableEntryOptions options = {
      .direction = TranslationDirection::kForController,
      .ir_p4_info = GetIrP4Info(),
      .translate_port_ids = false,
      .port_map = {},
      .cpu_queue_translator = *cpu_queue_translator,
  };

  EXPECT_OK(TranslateTableEntry(options, ir_table_entry));
  EXPECT_THAT(ir_table_entry, EqualsProto(original_table_entry));
}

TEST(TranslateTableEntry, FailsIfAppDbQueueIsNotAHexStringString) {
  pdpi::IrTableEntry ir_table_entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        table_name: "acl_ingress_table"
        matches {
          name: "is_ip"
          optional { value { hex_str: "0x1" } }
        }
        action {
          name: "acl_trap"
          params {
            name: "qos_queue"
            value { str: "ohhi" }  # str: <> should be hex-encoded number
          }
        }
      )pb",
      &ir_table_entry));
  TranslateTableEntryOptions options = {
      .direction = TranslationDirection::kForController,
      .ir_p4_info = GetIrP4Info(),
      .translate_port_ids = false,
      .port_map = {},
      .cpu_queue_translator = EmptyCpuQueueTranslator(),
  };
  EXPECT_FALSE(TranslateTableEntry(options, ir_table_entry).ok());
}

TEST(TranslateTableEntry, FailsIfAppDbQueueIsNotAString) {
  pdpi::IrTableEntry ir_table_entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        table_name: "acl_ingress_table"
        matches {
          name: "is_ip"
          optional { value { hex_str: "0x1" } }
        }
        action {
          name: "acl_trap"
          params {
            name: "qos_queue"
            value { hex_str: "0x1" }  # Wrong format (should be str)
          }
        }
      )pb",
      &ir_table_entry));
  TranslateTableEntryOptions options = {
      .direction = TranslationDirection::kForController,
      .ir_p4_info = GetIrP4Info(),
      .translate_port_ids = false,
      .port_map = {},
      .cpu_queue_translator = EmptyCpuQueueTranslator(),
  };
  EXPECT_FALSE(TranslateTableEntry(options, ir_table_entry).ok());
}

TEST(TranslatePacketReplication, FailsIfPacketReplicationHasDuplicateReplicas) {
  p4::v1::Entity pi_entity;
  // This packet replication entry is invalid, due to the duplicate replica.
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 1
            replicas { port: "Ethernet0" instance: 0 }
            replicas { port: "Ethernet0" instance: 0 }
          }
        }
      )pb",
      &pi_entity));

  EXPECT_FALSE(TranslatePiEntityForOrchAgent(
                   pi_entity, GetIrP4Info(), /*translate_port_ids=*/true,
                   /*port_translation_map=*/{}, EmptyCpuQueueTranslator(),
                   /*translate_key_only=*/false)
                   .ok());
}

TEST(TranslatePacketReplication, TranslatePortInReplicaToOaSuccess) {
  pdpi::IrPacketReplicationEngineEntry entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        multicast_group_entry {
          multicast_group_id: 1
          replicas { port: "1" instance: 0 }
        }
      )pb",
      &entry));

  boost::bimap<std::string, std::string> port_translation_map;
  port_translation_map.insert({"Ethernet0", "1"});
  TranslateTableEntryOptions options = {
      .direction = TranslationDirection::kForOrchAgent,
      .ir_p4_info = GetIrP4Info(),
      .translate_port_ids = true,
      .port_map = port_translation_map,
      .cpu_queue_translator = EmptyCpuQueueTranslator(),
  };
  pdpi::IrPacketReplicationEngineEntry updated = entry;
  updated.mutable_multicast_group_entry()->mutable_replicas(0)->set_port(
      "Ethernet0");

  EXPECT_OK(TranslatePacketReplicationEntry(options, entry));
  EXPECT_THAT(updated, EqualsProto(entry));
}

TEST(TranslatePacketReplication, TranslatePortInReplicaToControllerSuccess) {
  pdpi::IrPacketReplicationEngineEntry entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        multicast_group_entry {
          multicast_group_id: 1
          replicas { port: "Ethernet0" instance: 0 }
          replicas { port: "Ethernet1" instance: 0 }
        }
      )pb",
      &entry));

  boost::bimap<std::string, std::string> port_translation_map;
  port_translation_map.insert({"Ethernet0", "1"});
  port_translation_map.insert({"Ethernet1", "2"});
  TranslateTableEntryOptions options = {
      .direction = TranslationDirection::kForController,
      .ir_p4_info = GetIrP4Info(),
      .translate_port_ids = true,
      .port_map = port_translation_map,
      .cpu_queue_translator = EmptyCpuQueueTranslator(),
  };
  pdpi::IrPacketReplicationEngineEntry updated = entry;
  updated.mutable_multicast_group_entry()->mutable_replicas(0)->set_port("1");
  updated.mutable_multicast_group_entry()->mutable_replicas(1)->set_port("2");

  EXPECT_OK(TranslatePacketReplicationEntry(options, entry));
  EXPECT_THAT(updated, EqualsProto(entry));
}

TEST(TranslatePacketReplication, TranslatePortInReplicaToOaMissingPort) {
  pdpi::IrPacketReplicationEngineEntry entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        multicast_group_entry {
          multicast_group_id: 1
          replicas { port: "1" instance: 0 }
        }
      )pb",
      &entry));

  boost::bimap<std::string, std::string> port_translation_map;
  port_translation_map.insert({"Ethernet0", "555"});
  TranslateTableEntryOptions options = {
      .direction = TranslationDirection::kForController,
      .ir_p4_info = GetIrP4Info(),
      .translate_port_ids = true,
      .port_map = port_translation_map,
      .cpu_queue_translator = EmptyCpuQueueTranslator(),
  };
  EXPECT_THAT(TranslatePacketReplicationEntry(options, entry),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(TranslatePacketReplication, TranslatesReplicasToOa) {
  pdpi::IrEntity entry;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 7
            replicas { port: "1" instance: 5 }
            replicas { port: "2" instance: 6 }
          }
        }
      )pb",
      &entry));

  boost::bimap<std::string, std::string> port_translation_map;
  port_translation_map.insert({"Ethernet0", "1"});
  port_translation_map.insert({"Ethernet1", "2"});
  auto cpu_queue_translator = EmptyCpuQueueTranslator();

  EXPECT_OK(UpdateIrEntityForOrchAgent(
      entry, GetIrP4Info(), /*translate_port_ids=*/true, port_translation_map,
      cpu_queue_translator));

  // Expect that replica ports have changed.
  pdpi::IrEntity updated_entry = entry;
  updated_entry.mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry()
      ->mutable_replicas(0)
      ->set_port("Ethernet0");
  updated_entry.mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry()
      ->mutable_replicas(1)
      ->set_port("Ethernet1");
  EXPECT_THAT(updated_entry, EqualsProto(entry));
}

TEST(TranslateUnknown, UpdateEmptyEntityFails) {
  pdpi::IrEntity entry;
  auto cpu_queue_translator = EmptyCpuQueueTranslator();
  EXPECT_THAT(UpdateIrEntityForOrchAgent(entry, GetIrP4Info(),
                                         /*translate_port_ids=*/true,
                                         /*port_translation_map=*/{},
                                         cpu_queue_translator),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(TranslateEntity, UnsupportedEntityTypeFails) {
  p4::v1::Entity pi_entity;
  EXPECT_FALSE(TranslatePiEntityForOrchAgent(
                   pi_entity, GetIrP4Info(), /*translate_port_ids=*/true,
                   /*port_translation_map=*/{}, EmptyCpuQueueTranslator(),
                   /*translate_key_only=*/false)
                   .ok());
}

}  // namespace
}  // namespace p4rt_app

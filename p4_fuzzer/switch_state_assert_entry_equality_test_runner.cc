#include <functional>
#include <iostream>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "absl/types/span.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/testing/test_p4info.h"

namespace p4_fuzzer {
namespace {

using ::p4::config::v1::P4Info;
using ::p4::config::v1::Preamble;
using ::p4::config::v1::Table;
using ::p4::v1::Entity;
using ::p4::v1::TableEntry;
using ::pdpi::CreateIrP4Info;
using ::pdpi::IrEntity;
using ::pdpi::IrP4Info;
using ::pdpi::IrTableEntry;

constexpr char kGoldenName[] = "golden_table";

IrP4Info GetIrP4Info() {
  P4Info info;

  Table* spam_table = info.add_tables();
  Preamble* preamble = spam_table->mutable_preamble();
  preamble->set_id(1);
  preamble->set_alias(kGoldenName);
  p4::config::v1::MatchField* match_field =
      spam_table->mutable_match_fields()->Add();
  match_field->set_id(1);
  match_field->set_name("field1");
  match_field->set_bitwidth(32);
  match_field->set_match_type(p4::config::v1::MatchField::EXACT);

  return CreateIrP4Info(info).value();
}

struct TestCase {
  std::string description;
  std::vector<IrEntity> switch_entities;
  std::vector<IrEntity> fuzzer_entities;
  std::string mask_function_description;
  std::optional<std::function<bool(IrTableEntry, IrTableEntry)>> mask_function;
};

struct SwitchStateSummaryTestCase {
  std::string description;
  std::string info;
  IrP4Info ir_info;
  std::vector<IrEntity> entities;
  bool delete_entries;
};

std::vector<TestCase> TestCases() {
  std::vector<TestCase> test_cases;

  test_cases.emplace_back(TestCase{
      .description = "Switch Has Unique Entity",
      .switch_entities = {gutil::ParseProtoOrDie<IrEntity>(
          absl::Substitute(R"pb(
                             table_entry {
                               table_name: "$0"
                               matches {
                                 name: "field1"
                                 exact { hex_str: "0xbe0a0bed" }
                               }
                             }
                           )pb",
                           kGoldenName))},
      .fuzzer_entities = {},
  });

  test_cases.emplace_back(TestCase{
      .description = "Fuzzer Has Unique Entity",
      .switch_entities = {},
      .fuzzer_entities = {gutil::ParseProtoOrDie<IrEntity>(
          absl::Substitute(R"pb(
                             table_entry {
                               table_name: "$0"
                               matches {
                                 name: "field1"
                                 exact { hex_str: "0xbe0a0bed" }
                               }
                             }
                           )pb",
                           kGoldenName))},
  });

  test_cases.emplace_back(TestCase{
      .description =
          "Switch and Fuzzer entity have same key but different value",
      .switch_entities = {gutil::ParseProtoOrDie<IrEntity>(
          absl::Substitute(R"pb(
                             table_entry {
                               table_name: "$0"
                               matches {
                                 name: "field1"
                                 exact { hex_str: "0xbe0a0bed" }
                               }
                             }
                           )pb",
                           kGoldenName))},
      .fuzzer_entities = {gutil::ParseProtoOrDie<IrEntity>(
          absl::Substitute(R"pb(
                             table_entry {
                               table_name: "$0"
                               matches {
                                 name: "field1"
                                 exact { hex_str: "0xbe0a0bed" }
                               }
                               controller_metadata: "Am cookie, much wow"
                             }
                           )pb",
                           kGoldenName))},
  });

  test_cases.emplace_back(TestCase{
      .description = "Switch and Fuzzer have same entities",
      .switch_entities = {gutil::ParseProtoOrDie<IrEntity>(
          absl::Substitute(R"pb(
                             table_entry {
                               table_name: "$0"
                               matches {
                                 name: "field1"
                                 exact { hex_str: "0xbe0a0bed" }
                               }
                             }
                           )pb",
                           kGoldenName))},
      .fuzzer_entities = {gutil::ParseProtoOrDie<IrEntity>(
          absl::Substitute(R"pb(
                             table_entry {
                               table_name: "$0"
                               matches {
                                 name: "field1"
                                 exact { hex_str: "0xbe0a0bed" }
                               }
                             }
                           )pb",
                           kGoldenName))},
  });

  test_cases.emplace_back(TestCase{
      .description = "Missing metadata is ignored due to mask function",
      .switch_entities = {gutil::ParseProtoOrDie<IrEntity>(
          absl::Substitute(R"pb(
                             table_entry {
                               table_name: "$0"
                               matches {
                                 name: "field1"
                                 exact { hex_str: "0xbe0a0bed" }
                               }
                             }
                           )pb",
                           kGoldenName))},
      .fuzzer_entities = {gutil::ParseProtoOrDie<IrEntity>(
          absl::Substitute(R"pb(
                             table_entry {
                               table_name: "$0"
                               matches {
                                 name: "field1"
                                 exact { hex_str: "0xbe0a0bed" }
                               }
                               controller_metadata: "Am cookie, much wow"
                             }
                           )pb",
                           kGoldenName))},
      .mask_function_description = "Mask ignores metadata field",
      .mask_function =
          [](IrTableEntry a, IrTableEntry b) {
            google::protobuf::util::MessageDifferencer differ;
            differ.IgnoreField(IrTableEntry::descriptor()->FindFieldByName(
                "controller_metadata"));
            return differ.Compare(a, b);
          },
  });

  return test_cases;
}

std::vector<SwitchStateSummaryTestCase> SwitchStateSummaryTestCases() {
  std::vector<SwitchStateSummaryTestCase> test_cases;

  {
    test_cases.emplace_back(SwitchStateSummaryTestCase{
        .description = "Summary With No Resource Limits Hit",
        .info = "A single entry added to lpm1 table.",
        .ir_info = pdpi::GetTestIrP4Info(),
        .entities = {gutil::ParseProtoOrDie<IrEntity>(
            R"pb(
              table_entry {
                table_name: "lpm1_table"
                matches {
                  name: "ipv4"
                  lpm {
                    value { ipv4: "10.43.12.0" }
                    prefix_length: 24
                  }
                }
                action { name: "NoAction" }
              }
            )pb")},
        .delete_entries = false,
    });
  }

  // Exceeding max capacities for WCMP tables with SumOfWeights and
  // SumOfMembers size semantics.
  {
    IrP4Info ir_info_sum_of_weights = pdpi::GetTestIrP4Info();
    IrP4Info ir_info_sum_of_members = pdpi::GetTestIrP4Info();
    for (auto& [_, action_profile] :
         *ir_info_sum_of_members.mutable_action_profiles_by_id()) {
      action_profile.mutable_action_profile()
          ->mutable_sum_of_members()
          ->set_max_member_weight(4096);
    }

    // Relevant constants.
    const uint32_t kWcmpTableId = 33554438;
    uint32_t wcmp_table_size =
        gutil::FindOrDie(ir_info_sum_of_weights.tables_by_id(), kWcmpTableId)
            .size();
    int32_t per_action_weight = 10;  // > 0

    std::vector<IrEntity> excessive_entries;
    excessive_entries.reserve(wcmp_table_size);
    // Construct sufficiently many unique WCMP table entries.
    for (int i = 0; i < wcmp_table_size + 1; i++) {
      excessive_entries.push_back(
          gutil::ParseProtoOrDie<IrEntity>(absl::Substitute(
              R"pb(
                table_entry {
                  table_name: "wcmp_table"
                  matches {
                    name: "ipv4"
                    lpm {
                      value { ipv4: "$0.$1.$2.$3" }
                      prefix_length: 32
                    }
                  }
                  action_set {
                    actions {
                      action {
                        name: "do_thing_1"
                        params {
                          name: "arg2"
                          value { hex_str: "0x00307831" }
                        }
                        params {
                          name: "arg1"
                          value { hex_str: "0x00307832" }
                        }
                      }
                      weight: $4
                    }
                  }
                }
              )pb",
              absl::StrCat((i >> 24) % (1 << 8)),
              absl::StrCat((i >> 16) % (1 << 8)),
              absl::StrCat((i >> 8) % (1 << 8)), absl::StrCat(i % (1 << 8)),
              absl::StrCat(per_action_weight))));
    }

    test_cases.emplace_back(SwitchStateSummaryTestCase{
        .description =
            "Summary With Resource Limits Hit using Sum Of Weights Semantics",
        .info = "Excessive entries added to wcmp table.",
        .ir_info = ir_info_sum_of_weights,
        .entities = excessive_entries,
        .delete_entries = false,
    });

    test_cases.emplace_back(SwitchStateSummaryTestCase{
        .description = "Summary With Resource Limits Hit using Sum Of Weights "
                       "Semantics and all entries cleared.",
        .info = "Excessive entries added to wcmp table then removed. Still "
                "notes that resource limits reached.",
        .ir_info = ir_info_sum_of_weights,
        .entities = excessive_entries,
        .delete_entries = true,
    });

    test_cases.emplace_back(SwitchStateSummaryTestCase{
        .description =
            "Summary With Resource Limits Hit using Sum Of Members Semantics",
        .info = "Excessive entries added to wcmp table.",
        .ir_info = ir_info_sum_of_members,
        .entities = excessive_entries,
        .delete_entries = false,
    });

    test_cases.emplace_back(SwitchStateSummaryTestCase{
        .description = "Summary With Resource Limits Hit using Sum Of Members "
                       "Semantics and all entries cleared.",
        .info = "Excessive entries added to wcmp table.",
        .ir_info = ir_info_sum_of_members,
        .entities = excessive_entries,
        .delete_entries = true,
    });
  }

  // Multicast table summaries.
  {
    const int kMulticastGroupTableSize = 256;
    const int kMulticastGroupTableTotalReplicas = 2048;
    const int kMulticastGroupTableMaxReplicasPerEntry = 8;

    IrP4Info ir_info_multicast = pdpi::GetTestIrP4Info();
    ::p4::config::v1::PlatformProperties& platform_properties =
        *ir_info_multicast.mutable_pkg_info()->mutable_platform_properties();
    platform_properties.set_multicast_group_table_size(
        kMulticastGroupTableSize);
    platform_properties.set_multicast_group_table_total_replicas(
        kMulticastGroupTableTotalReplicas);
    platform_properties.set_multicast_group_table_max_replicas_per_entry(
        kMulticastGroupTableMaxReplicasPerEntry);

    test_cases.emplace_back(SwitchStateSummaryTestCase{
        .description = "Summary With No Multicast Resource Guarantees Hit",
        .info = "A single multicast entry added.",
        .ir_info = ir_info_multicast,
        .entities = {gutil::ParseProtoOrDie<IrEntity>(
            R"pb(
              packet_replication_engine_entry {
                multicast_group_entry {
                  multicast_group_id: 7
                  replicas { port: "earth" }
                  replicas { port: "water" }
                  replicas { port: "fire" }
                  replicas { port: "air" }
                }
              }
            )pb")},
        .delete_entries = false,
    });

    std::vector<IrEntity> excessive_entries;
    excessive_entries.reserve(kMulticastGroupTableSize + 1);
    // Construct sufficiently many unique multicast group table entries.
    for (int i = 0; i < kMulticastGroupTableSize + 1; ++i) {
      IrEntity multicast_entity;
      multicast_entity.mutable_packet_replication_engine_entry()
          ->mutable_multicast_group_entry()
          ->set_multicast_group_id(i);
      for (int j = 0; j < kMulticastGroupTableMaxReplicasPerEntry + 1; ++j) {
        multicast_entity.mutable_packet_replication_engine_entry()
            ->mutable_multicast_group_entry()
            ->add_replicas()
            ->set_port(absl::StrCat("port: ", j));
      }
      excessive_entries.push_back(multicast_entity);
    }

    test_cases.emplace_back(SwitchStateSummaryTestCase{
        .description = "Summary With Multicast Resource Guarantees Hit",
        .info =
            "Excessive entries and replicas added to mulitcast group table.",
        .ir_info = ir_info_multicast,
        .entities = excessive_entries,
        .delete_entries = false,
    });

    test_cases.emplace_back(SwitchStateSummaryTestCase{
        .description = "Summary With Multicast Resource Limits Hit and all "
                       "entries cleared.",
        .info =
            "Excessive entries and replicas added to mulitcast group table.",
        .ir_info = ir_info_multicast,
        .entities = excessive_entries,
        .delete_entries = true,
    });
  }

  return test_cases;
}

std::string EntitiesToString(absl::Span<const IrEntity> entities) {
  std::string result = "";
  for (const auto& entity : entities) {
    absl::StrAppend(&result, gutil::PrintTextProto(entity));
  }
  return result;
}

absl::StatusOr<std::vector<Entity>> IrToPiVector(
    absl::Span<const IrEntity> ir_entities, const IrP4Info& ir_info) {
  std::vector<Entity> pi_entities;
  for (const auto& ir_entity : ir_entities) {
    ASSIGN_OR_RETURN(Entity pi_entity, pdpi::IrEntityToPi(ir_info, ir_entity));
    pi_entities.push_back(pi_entity);
  }
  return pi_entities;
}

absl::Status main() {
  IrP4Info ir_info = GetIrP4Info();
  SwitchState state(ir_info);

  for (const auto& test : TestCases()) {
    state.ClearTableEntries();

    ASSIGN_OR_RETURN(std::vector<Entity> pi_fuzzer_entities,
                     IrToPiVector(test.fuzzer_entities, ir_info));
    ASSIGN_OR_RETURN(std::vector<Entity> pi_switch_entities,
                     IrToPiVector(test.switch_entities, ir_info));

    RETURN_IF_ERROR(state.SetEntities(pi_fuzzer_entities));
    RETURN_IF_ERROR(state.CheckConsistency());

    // TODO: b/316926338 - Remove once switch state is refactored to use
    // entities first.
    std::vector<TableEntry> table_entries;
    for (const auto& entity : pi_switch_entities) {
      if (entity.has_table_entry()) {
        table_entries.push_back(entity.table_entry());
      }
    }

    std::cout << "#########################################################\n"
              << "### Test Case: " << test.description << "\n"
              << "#########################################################\n\n"
              << "=== Switch Entities ===\n"
              << EntitiesToString(test.switch_entities) << "\n"
              << "=== Fuzzer Entities ===\n"
              << EntitiesToString(test.fuzzer_entities) << "\n"
              << "=== Mask Function ===\n"
              << (test.mask_function.has_value()
                      ? test.mask_function_description
                      : "No mask function was used")
              << "\n\n"
              << "=== Test Output ===\n"
              << gutil::StableStatusToString(state.AssertEntriesAreEqualToState(
                     table_entries, test.mask_function))
              << "\n";
  }

  for (const auto& test : SwitchStateSummaryTestCases()) {
    state = SwitchState(test.ir_info);
    ASSIGN_OR_RETURN(std::vector<Entity> pi_entities,
                     IrToPiVector(test.entities, test.ir_info));
    RETURN_IF_ERROR(state.SetEntities(pi_entities));
    RETURN_IF_ERROR(state.CheckConsistency());
    if (test.delete_entries) {
      state.ClearTableEntries();
    }

    std::cout << "#########################################################\n"
              << "### Test Case: " << test.description << "\n"
              << "### info: " << test.info << "\n"
              << "#########################################################\n\n"
              << "=== Switch State Summary ===\n"
              << state.SwitchStateSummary() << "\n\n";
  }

  return absl::OkStatus();
}

}  // namespace
}  // namespace p4_fuzzer

int main() {
  absl::Status status = p4_fuzzer::main();
  if (!status.ok()) {
    std::cout << status;
  }
}

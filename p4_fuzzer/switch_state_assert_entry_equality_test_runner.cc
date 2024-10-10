#include <functional>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "absl/types/span.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/collections.h"
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
using ::p4::v1::TableEntry;
using ::pdpi::CreateIrP4Info;
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
  std::vector<IrTableEntry> switch_entries;
  std::vector<IrTableEntry> fuzzer_entries;
  std::string mask_function_description;
  std::optional<std::function<bool(IrTableEntry, IrTableEntry)>> mask_function;
};

struct SwitchStateSummaryTestCase {
  std::string description;
  std::string info;
  IrP4Info ir_info;
  std::vector<IrTableEntry> entries;
  bool delete_entries;
};

std::vector<TestCase> TestCases() {
  std::vector<TestCase> test_cases;

  test_cases.emplace_back(TestCase{
      .description = "Switch Has Unique Entry",
      .switch_entries = {gutil::ParseProtoOrDie<IrTableEntry>(
          absl::Substitute(R"pb(
                             table_name: "$0"
                             matches {
                               name: "field1"
                               exact { hex_str: "0xbe0a0bed" }
                             }
                           )pb",
                           kGoldenName))},
      .fuzzer_entries = {},
  });

  test_cases.emplace_back(TestCase{
      .description = "Fuzzer Has Unique Entry",
      .switch_entries = {},
      .fuzzer_entries = {gutil::ParseProtoOrDie<IrTableEntry>(
          absl::Substitute(R"pb(
                             table_name: "$0"
                             matches {
                               name: "field1"
                               exact { hex_str: "0xbe0a0bed" }
                             }
                           )pb",
                           kGoldenName))},
  });

  test_cases.emplace_back(TestCase{
      .description =
          "Switch and Fuzzer entry have same key but different value",
      .switch_entries = {gutil::ParseProtoOrDie<IrTableEntry>(
          absl::Substitute(R"pb(
                             table_name: "$0"
                             matches {
                               name: "field1"
                               exact { hex_str: "0xbe0a0bed" }
                             }
                           )pb",
                           kGoldenName))},
      .fuzzer_entries = {gutil::ParseProtoOrDie<IrTableEntry>(
          absl::Substitute(R"pb(
                             table_name: "$0"
                             matches {
                               name: "field1"
                               exact { hex_str: "0xbe0a0bed" }
                             }
                             controller_metadata: "Am cookie, much wow"
                           )pb",
                           kGoldenName))},
  });

  test_cases.emplace_back(TestCase{
      .description = "Switch and Fuzzer have same entries",
      .switch_entries = {gutil::ParseProtoOrDie<IrTableEntry>(
          absl::Substitute(R"pb(
                             table_name: "$0"
                             matches {
                               name: "field1"
                               exact { hex_str: "0xbe0a0bed" }
                             }
                           )pb",
                           kGoldenName))},
      .fuzzer_entries = {gutil::ParseProtoOrDie<IrTableEntry>(
          absl::Substitute(R"pb(
                             table_name: "$0"
                             matches {
                               name: "field1"
                               exact { hex_str: "0xbe0a0bed" }
                             }
                           )pb",
                           kGoldenName))},
  });

  test_cases.emplace_back(TestCase{
      .description = "Missing metadata is ignored due to mask function",
      .switch_entries = {gutil::ParseProtoOrDie<IrTableEntry>(
          absl::Substitute(R"pb(
                             table_name: "$0"
                             matches {
                               name: "field1"
                               exact { hex_str: "0xbe0a0bed" }
                             }
                           )pb",
                           kGoldenName))},
      .fuzzer_entries = {gutil::ParseProtoOrDie<IrTableEntry>(
          absl::Substitute(R"pb(
                             table_name: "$0"
                             matches {
                               name: "field1"
                               exact { hex_str: "0xbe0a0bed" }
                             }
                             controller_metadata: "Am cookie, much wow"
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
        .entries = {gutil::ParseProtoOrDie<IrTableEntry>(
            R"pb(table_name: "lpm1_table"
                 matches {
                   name: "ipv4"
                   lpm {
                     value { ipv4: "10.43.12.0" }
                     prefix_length: 24
                   }
                 }
                 action { name: "NoAction" }
            )pb")},
        .delete_entries = false,
    });
  }

  // Exceeding max capacities for WCMP tables with SUM_OF_WEIGHTS and
  // SUM_OF_MEMBERS size semantics.
  {
    IrP4Info ir_info_sum_of_weights = pdpi::GetTestIrP4Info();
    IrP4Info ir_info_sum_of_members = pdpi::GetTestIrP4Info();
    for (auto& [_, action_profile] :
         *ir_info_sum_of_members.mutable_action_profiles_by_id()) {
            action_profile.mutable_action_profile()->mutable_sum_of_members()->set_max_member_weight(4096);
    }

    // Relevant constants.
    const uint32_t kWcmpTableId = 33554438;
    uint32_t wcmp_table_size =
        gutil::FindOrDie(ir_info_sum_of_weights.tables_by_id(), kWcmpTableId)
            .size();
    int32_t per_action_weight = 10;  // > 0

    std::vector<IrTableEntry> excessive_entries;
    excessive_entries.reserve(wcmp_table_size);
    // Construct sufficiently many unique WCMP table entries.
    for (int i = 0; i < wcmp_table_size + 1; i++) {
      excessive_entries.push_back(
          gutil::ParseProtoOrDie<IrTableEntry>(absl::Substitute(
              R"pb(
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
        .entries = excessive_entries,
        .delete_entries = false,
    });

    test_cases.emplace_back(SwitchStateSummaryTestCase{
        .description = "Summary With Resource Limits Hit using Sum Of Weights "
                       "Semantics and all entries cleared.",
        .info = "Excessive entries added to wcmp table then removed. Still "
                "notes that resource limits reached.",
        .ir_info = ir_info_sum_of_weights,
        .entries = excessive_entries,
        .delete_entries = true,
    });

    test_cases.emplace_back(SwitchStateSummaryTestCase{
        .description =
            "Summary With Resource Limits Hit using Sum Of Members Semantics",
        .info = "Excessive entries added to wcmp table.",
        .ir_info = ir_info_sum_of_members,
        .entries = excessive_entries,
        .delete_entries = false,
    });

    test_cases.emplace_back(SwitchStateSummaryTestCase{
        .description = "Summary With Resource Limits Hit using Sum Of Members "
                       "Semantics and all entries cleared.",
        .info = "Excessive entries added to wcmp table.",
        .ir_info = ir_info_sum_of_members,
        .entries = excessive_entries,
        .delete_entries = true,
    });
  }

  return test_cases;
}

std::string EntriesToString(absl::Span<const IrTableEntry> entries) {
  std::string result = "";
  for (const auto& entry : entries) {
    absl::StrAppend(&result, gutil::PrintTextProto(entry));
  }
  return result;
}

absl::StatusOr<std::vector<TableEntry>> IrToPiVector(
    absl::Span<const IrTableEntry> ir_entries, const IrP4Info& ir_info) {
  std::vector<TableEntry> pi_entries;
  for (const auto& ir_entry : ir_entries) {
    ASSIGN_OR_RETURN(TableEntry pi_entry,
                     pdpi::IrTableEntryToPi(ir_info, ir_entry));
    pi_entries.push_back(pi_entry);
  }
  return pi_entries;
}

absl::Status main() {
  IrP4Info ir_info = GetIrP4Info();
  SwitchState state(ir_info);

  for (const auto& test : TestCases()) {
    state.ClearTableEntries();

    ASSIGN_OR_RETURN(std::vector<TableEntry> pi_fuzzer_entries,
                     IrToPiVector(test.fuzzer_entries, ir_info));
    ASSIGN_OR_RETURN(std::vector<TableEntry> pi_switch_entries,
                     IrToPiVector(test.switch_entries, ir_info));

    RETURN_IF_ERROR(state.SetTableEntries(pi_fuzzer_entries));
    RETURN_IF_ERROR(state.CheckConsistency());

    std::cout << "#########################################################\n"
              << "### Test Case: " << test.description << "\n"
              << "#########################################################\n\n"
              << "=== Switch Entries ===\n"
              << EntriesToString(test.switch_entries) << "\n"
              << "=== Fuzzer Entries ===\n"
              << EntriesToString(test.fuzzer_entries) << "\n"
              << "=== Mask Function ===\n"
              << (test.mask_function.has_value()
                      ? test.mask_function_description
                      : "No mask function was used")
              << "\n\n"
              << "=== Test Output ===\n"
              << gutil::StableStatusToString(state.AssertEntriesAreEqualToState(
                     pi_switch_entries, test.mask_function))
              << "\n";
  }

  for (const auto& test : SwitchStateSummaryTestCases()) {
    state = SwitchState(test.ir_info);
    ASSIGN_OR_RETURN(std::vector<TableEntry> pi_entries,
                     IrToPiVector(test.entries, test.ir_info));
    RETURN_IF_ERROR(state.SetTableEntries(pi_entries));
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

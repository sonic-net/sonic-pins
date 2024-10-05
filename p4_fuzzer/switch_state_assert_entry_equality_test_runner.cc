#include <functional>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
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

void PrintEntries(absl::Span<const IrTableEntry> entries) {
  for (const auto& entry : entries) {
    std::cout << gutil::PrintTextProto(entry);
  }
  std::cout << "\n";
}

absl::StatusOr<std::vector<p4::v1::TableEntry>> IrToPiVector(
    absl::Span<const IrTableEntry> ir_entries, const IrP4Info& ir_info) {
  std::vector<p4::v1::TableEntry> pi_entries;
  for (const auto& ir_entry : ir_entries) {
    ASSIGN_OR_RETURN(p4::v1::TableEntry pi_entry,
                     pdpi::IrTableEntryToPi(ir_info, ir_entry));
    pi_entries.push_back(pi_entry);
  }
  return pi_entries;
}

absl::Status main() {
  IrP4Info ir_info = GetIrP4Info();
  SwitchState state(ir_info);
  absl::Status status;

  for (const auto& test : TestCases()) {
    state.ClearTableEntries();

    ASSIGN_OR_RETURN(std::vector<p4::v1::TableEntry> pi_fuzzer_entries,
                     IrToPiVector(test.fuzzer_entries, ir_info));
    ASSIGN_OR_RETURN(std::vector<p4::v1::TableEntry> pi_switch_entries,
                     IrToPiVector(test.switch_entries, ir_info));

    RETURN_IF_ERROR(state.SetTableEntries(pi_fuzzer_entries));
    RETURN_IF_ERROR(state.CheckConsistency());

    std::cout << "#########################################################\n"
              << "### Test Case: " << test.description << "\n"
              << "#########################################################\n\n"
              << "=== Switch Entries ===\n";
    PrintEntries(test.switch_entries);
    std::cout << "=== Fuzzer Entries ===\n";
    PrintEntries(test.fuzzer_entries);
    std::cout << "=== Mask Function ===\n";
    if (test.mask_function.has_value()) {
      std::cout << test.mask_function_description << "\n\n";
    } else {
      std::cout << "No mask function was used\n\n";
    }
    std::cout << "=== Test Output ===\n"
              << gutil::StableStatusToString(state.AssertEntriesAreEqualToState(
                     pi_switch_entries, test.mask_function))
              << "\n";
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

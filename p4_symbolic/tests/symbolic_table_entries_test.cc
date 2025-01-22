// Copyright 2024 Google LLC
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

#include <memory>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/ir/parser.h"
#include "p4_symbolic/ir/table_entries.h"
#include "p4_symbolic/sai/sai.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/table_entry.h"
#include "p4_symbolic/symbolic/values.h"
#include "p4_symbolic/test_util.h"
#include "thinkit/bazel_test_environment.h"
#include "thinkit/test_environment.h"

namespace p4_symbolic {
namespace {

class SymbolicTableEntriesIPv4BasicTest : public testing::Test {
 public:
  thinkit::TestEnvironment& Environment() { return *environment_; }

  void SetUp() override {
    constexpr absl::string_view bmv2_json_path =
        "p4_symbolic/testdata/ipv4-routing/"
        "basic.config.json";
    constexpr absl::string_view p4info_path =
        "p4_symbolic/testdata/ipv4-routing/"
        "basic.p4info.pb.txt";
    constexpr absl::string_view entries_path =
        "p4_symbolic/testdata/ipv4-routing/"
        "entries.pb.txt";
    ASSERT_OK_AND_ASSIGN(
        p4::v1::ForwardingPipelineConfig config,
        ParseToForwardingPipelineConfig(bmv2_json_path, p4info_path));
    ASSERT_OK_AND_ASSIGN(
        std::vector<p4::v1::TableEntry> pi_entries,
        GetPiTableEntriesFromPiUpdatesProtoTextFile(entries_path));
    ASSERT_OK_AND_ASSIGN(ir::Dataplane dataplane,
                         ir::ParseToIr(config, pi_entries));
    program_ = std::move(dataplane.program);
    ir_entries_ = std::move(dataplane.entries);
  }

 protected:
  std::unique_ptr<thinkit::TestEnvironment> environment_ =
      std::make_unique<thinkit::BazelTestEnvironment>(
          /*mask_known_failures=*/true);
  ir::P4Program program_;
  ir::TableEntries ir_entries_;
};

TEST_F(SymbolicTableEntriesIPv4BasicTest, OneSymbolicEntryPerTable) {
  constexpr int priority = 0;
  constexpr int prefix_length = 16;

  // Create a symbolic IR entry for each table.
  ir_entries_.clear();
  for (const auto& [table_name, table] : program_.tables()) {
    ASSERT_OK_AND_ASSIGN(
        ir::TableEntry ir_entry,
        symbolic::CreateSymbolicIrTableEntry(table, priority, prefix_length));
    ir_entries_[table_name].push_back(std::move(ir_entry));
  }

  // Symbolically evaluate the program with symbolic table entries.
  std::vector<int> ports = {1, 2, 3, 4, 5};
  symbolic::TranslationPerType translations;
  translations[p4_symbolic::kPortIdTypeName] =
      symbolic::values::TranslationData{
          .static_mapping = {{"1", 1}, {"2", 2}, {"3", 3}, {"4", 4}, {"5", 5}},
          .dynamic_translation = false,
      };
  translations[p4_symbolic::kVrfIdTypeName] = symbolic::values::TranslationData{
      .static_mapping = {{"", 0}},
      .dynamic_translation = true,
  };
  LOG(INFO) << "Building model ...";
  absl::Time start_time = absl::Now();
  EXPECT_THAT(
      symbolic::EvaluateP4Program(program_, ir_entries_, ports, translations),
      gutil::StatusIs(absl::StatusCode::kUnimplemented,
                      "Symbolic entries are not supported at the moment."));
  LOG(INFO) << "-> done in " << (absl::Now() - start_time);
}

}  // namespace
}  // namespace p4_symbolic

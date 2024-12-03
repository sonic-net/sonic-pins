#include "p4_symbolic/ir/cfg.h"

#include <memory>

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/status_matchers.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"

namespace p4_symbolic::ir {
namespace {

using gutil::StatusIs;
using testing::ValuesIn;

struct CfgTestParam {
  // Expected field values in OptimizedSymbolicExecutionInfo for a certain
  // control point.
  struct ExpectedInfo {
    std::string merge_point;
    bool continue_to_merge_point;
  };

  std::string test_name;
  // The map of control_name to expected symbolic execution info only for
  // control points that we care about.
  absl::btree_map<std::string, ExpectedInfo> control_to_expected_info;
  // Text proto representing the input IR P4Program. A full program is not
  // necessary. It only needs to contain enough information to build the CFG.
  std::string ir_program_text_proto;
};

absl::StatusOr<P4Program> ReplaceEopAndParseProgramTextProto(
    absl::string_view ir_program_text_proto) {
  return gutil::ParseTextProto<P4Program>(absl::StrReplaceAll(
      ir_program_text_proto,
      {
          {"$eoparser", absl::Substitute("\"$0\"", EndOfParser())},
          {"$eop", absl::Substitute("\"$0\"", EndOfPipeline())},
      }));
}

using CfgTest = ::testing::TestWithParam<CfgTestParam>;
std::vector<CfgTestParam> GetCfgTestInstances() {
  return {
      {
          /*  t1 - ingress
           *   |
           *  t2 - eop
           */
          .test_name = "ProgramWithSequentialTables",
          .control_to_expected_info =
              {
                  {"t1", {"t2", true}},
                  {"t2", {EndOfPipeline(), true}},
              },
          .ir_program_text_proto = R"pb(
            pipeline {
              key: "ingress"
              value { name: "ingress" initial_control: "t1" }
            }
            parsers {
              key: "parser"
              value { name: "parser" initial_state: $eoparser }
            }
            tables {
              key: "t1"
              value {
                table_implementation { action_to_next_control { value: "t2" } }
              }
            }
            tables {
              key: "t2"
              value {
                table_implementation { action_to_next_control { value: $eop } }
              }
            }
          )pb",
      },
      {
          /*    c1 - ingress
           *   /  \
           *  t1  t2
           *   \  /
           *    t3 - eop
           */
          .test_name = "ProgramWithTableAfterConditional",
          .control_to_expected_info =
              {
                  {"c1", {"t3", true}},
                  {"t1", {"t3", false}},
                  {"t2", {"t3", false}},
                  {"t3", {EndOfPipeline(), true}},
              },
          .ir_program_text_proto = R"pb(
            pipeline {
              key: "ingress"
              value { name: "ingress" initial_control: "c1" }
            }
            parsers {
              key: "parser"
              value { name: "parser" initial_state: $eoparser }
            }
            conditionals {
              key: "c1"
              value { name: "c1" if_branch: "t1" else_branch: "t2" }
            }
            tables {
              key: "t1"
              value {
                table_implementation { action_to_next_control { value: "t3" } }
              }
            }
            tables {
              key: "t2"
              value {
                table_implementation { action_to_next_control { value: "t3" } }
              }
            }
            tables {
              key: "t3"
              value {
                table_implementation { action_to_next_control { value: $eop } }
              }
            }
          )pb",
      },
      {
          /*    c1 - ingress
           *   / |
           *  t1 |
           *   \ |
           *    t2 - eop
           */
          .test_name = "ProgramWithConditionalWithoutElse",
          .control_to_expected_info =
              {
                  {"c1", {"t2", true}},
                  {"t1", {"t2", false}},
                  {"t2", {EndOfPipeline(), true}},
              },
          .ir_program_text_proto = R"pb(
            pipeline {
              key: "ingress"
              value { name: "ingress" initial_control: "c1" }
            }
            parsers {
              key: "parser"
              value { name: "parser" initial_state: $eoparser }
            }
            conditionals {
              key: "c1"
              value { name: "c1" if_branch: "t1" else_branch: "t2" }
            }
            tables {
              key: "t1"
              value {
                table_implementation { action_to_next_control { value: "t2" } }
              }
            }
            tables {
              key: "t2"
              value {
                table_implementation { action_to_next_control { value: $eop } }
              }
            }
          )pb",
      },
      {
          /*    t1 - ingress
           *    |
           *    c1
           *   /  \
           *  t2   t3
           *  |    /
           *  t4  /
           *   \ /
           *    t5 - eop
           */
          .test_name = "ProgramWithCombinationOfSequentialTablesAndBranching",
          .control_to_expected_info =
              {
                  {"t1", {"c1", true}},
                  {"c1", {"t5", true}},
                  {"t2", {"t4", true}},
                  {"t3", {"t5", false}},
                  {"t4", {"t5", false}},
                  {"t5", {EndOfPipeline(), true}},
              },
          .ir_program_text_proto = R"pb(
            pipeline {
              key: "ingress"
              value { name: "ingress" initial_control: "t1" }
            }
            parsers {
              key: "parser"
              value { name: "parser" initial_state: $eoparser }
            }
            tables {
              key: "t1"
              value {
                table_implementation { action_to_next_control { value: "c1" } }
              }
            }
            conditionals {
              key: "c1"
              value { name: "c1" if_branch: "t2" else_branch: "t3" }
            }
            tables {
              key: "t2"
              value {
                table_implementation { action_to_next_control { value: "t4" } }
              }
            }
            tables {
              key: "t3"
              value {
                table_implementation { action_to_next_control { value: "t5" } }
              }
            }
            tables {
              key: "t4"
              value {
                table_implementation { action_to_next_control { value: "t5" } }
              }
            }
            tables {
              key: "t5"
              value {
                table_implementation { action_to_next_control { value: $eop } }
              }
            }
          )pb",
      },
      {
          /*     c1 - ingress
           *    /   \
           *  c2     t3
           *  / \    /
           * t1 t2  /
           *  \ /  /
           *   t4 /
           *    \/
           *    t5 - eop
           */
          .test_name = "ProgramWithNestedBranching",
          .control_to_expected_info =
              {
                  {"c1", {"t5", true}},
                  {"c2", {"t4", true}},
                  {"t1", {"t4", false}},
                  {"t2", {"t4", false}},
                  {"t3", {"t5", false}},
                  {"t4", {"t5", false}},
                  {"t5", {EndOfPipeline(), true}},
              },
          .ir_program_text_proto = R"pb(
            pipeline {
              key: "ingress"
              value { name: "ingress" initial_control: "c1" }
            }
            parsers {
              key: "parser"
              value { name: "parser" initial_state: $eoparser }
            }
            conditionals {
              key: "c1"
              value { name: "c1" if_branch: "c2" else_branch: "t3" }
            }
            conditionals {
              key: "c2"
              value { name: "c2" if_branch: "t1" else_branch: "t2" }
            }
            tables {
              key: "t1"
              value {
                table_implementation { action_to_next_control { value: "t4" } }
              }
            }
            tables {
              key: "t2"
              value {
                table_implementation { action_to_next_control { value: "t4" } }
              }
            }
            tables {
              key: "t3"
              value {
                table_implementation { action_to_next_control { value: "t5" } }
              }
            }
            tables {
              key: "t4"
              value {
                table_implementation { action_to_next_control { value: "t5" } }
              }
            }
            tables {
              key: "t5"
              value {
                table_implementation { action_to_next_control { value: $eop } }
              }
            }
          )pb",
      },
      {
          /*     c1 - ingress
           *    /  \
           *  c2    t3
           *  / \   /
           * t1 t2 /
           *  \ / /
           *   t4 - eop
           */
          .test_name = "ProgramWithSharedMergePoint",
          .control_to_expected_info =
              {
                  {"c1", {"t4", true}},
                  {"c2", {"t4", false}},
                  {"t1", {"t4", false}},
                  {"t2", {"t4", false}},
                  {"t3", {"t4", false}},
                  {"t4", {EndOfPipeline(), true}},
              },
          .ir_program_text_proto = R"pb(
            pipeline {
              key: "ingress"
              value { name: "ingress" initial_control: "c1" }
            }
            parsers {
              key: "parser"
              value { name: "parser" initial_state: $eoparser }
            }
            conditionals {
              key: "c1"
              value { name: "c1" if_branch: "c2" else_branch: "t3" }
            }
            conditionals {
              key: "c2"
              value { name: "c2" if_branch: "t1" else_branch: "t2" }
            }
            tables {
              key: "t1"
              value {
                table_implementation { action_to_next_control { value: "t4" } }
              }
            }
            tables {
              key: "t2"
              value {
                table_implementation { action_to_next_control { value: "t4" } }
              }
            }
            tables {
              key: "t3"
              value {
                table_implementation { action_to_next_control { value: "t4" } }
              }
            }
            tables {
              key: "t4"
              value {
                table_implementation { action_to_next_control { value: $eop } }
              }
            }
          )pb",
      },
      {
          /*    c1 - ingress
           *   /  \
           *  t1  t2
           *   \  /
           *    c2
           *   /  \
           *  t3  t4
           *   \  /
           *    t5 - eop
           */
          .test_name = "ProgramWithBranchOnMergePoint",
          .control_to_expected_info =
              {
                  {"c1", {"c2", true}},
                  {"t1", {"c2", false}},
                  {"t2", {"c2", false}},
                  {"c2", {"t5", true}},
                  {"t3", {"t5", false}},
                  {"t3", {"t5", false}},
                  {"t5", {EndOfPipeline(), true}},
              },
          .ir_program_text_proto = R"pb(
            pipeline {
              key: "ingress"
              value { name: "ingress" initial_control: "c1" }
            }
            parsers {
              key: "parser"
              value { name: "parser" initial_state: $eoparser }
            }
            conditionals {
              key: "c1"
              value { name: "c1" if_branch: "t1" else_branch: "t2" }
            }
            tables {
              key: "t1"
              value {
                table_implementation { action_to_next_control { value: "c2" } }
              }
            }
            tables {
              key: "t2"
              value {
                table_implementation { action_to_next_control { value: "c2" } }
              }
            }
            conditionals {
              key: "c2"
              value { name: "c2" if_branch: "t3" else_branch: "t4" }
            }
            tables {
              key: "t3"
              value {
                table_implementation { action_to_next_control { value: "t5" } }
              }
            }
            tables {
              key: "t4"
              value {
                table_implementation { action_to_next_control { value: "t5" } }
              }
            }
            tables {
              key: "t5"
              value {
                table_implementation { action_to_next_control { value: $eop } }
              }
            }
          )pb",
      },
      {
          /*  eop - ingress
           *
           *  start - parser
           *   |
           *  eoparser
           */
          .test_name = "ParserWithDefaultTransition",
          .control_to_expected_info =
              {
                  {"start", {EndOfParser(), true}},
              },
          .ir_program_text_proto = R"pb(
            pipeline {
              key: "ingress"
              value { name: "ingress" initial_control: $eop }
            }
            parsers {
              key: "parser"
              value {
                name: "parser"
                initial_state: "start"
                parse_states {
                  key: "start"
                  value {
                    name: "start"
                    parser_ops {
                      extract { header { header_name: "ethernet" } }
                    }
                    transitions { default_transition { next_state: $eoparser } }
                  }
                }
              }
            }
          )pb",
      },
      {
          /*  eop - ingress
           *
           *  start - parser
           *   |  \
           *   |  parse_ipv4
           *   |  /
           *  eoparser
           */
          .test_name = "ParserWithHexStringTransition",
          .control_to_expected_info =
              {
                  {"start", {EndOfParser(), true}},
                  {"parse_ipv4", {EndOfParser(), false}},
              },
          .ir_program_text_proto = R"pb(
            pipeline {
              key: "ingress"
              value { name: "ingress" initial_control: $eop }
            }
            parsers {
              key: "parser"
              value {
                name: "parser"
                initial_state: "start"
                parse_states {
                  key: "parse_ipv4"
                  value {
                    name: "parse_ipv4"
                    parser_ops { extract { header { header_name: "ipv4" } } }
                    transitions { default_transition { next_state: $eoparser } }
                  }
                }
                parse_states {
                  key: "start"
                  value {
                    name: "start"
                    parser_ops {
                      extract { header { header_name: "ethernet" } }
                    }
                    transition_key_fields {
                      field { header_name: "ethernet" field_name: "ether_type" }
                    }
                    transitions {
                      hex_string_transition {
                        value { value: "0x0800" }
                        mask {}
                        next_state: "parse_ipv4"
                      }
                    }
                    transitions { default_transition { next_state: $eoparser } }
                  }
                }
              }
            }
          )pb",
      },
      {
          /*
           *  start - parser
           *   |  \
           *   |  parse_ipv4
           *   |  /
           *  eoparser
           *
           *    c1 - ingress
           *   /  \
           *  t1  t2
           *   \  /
           *    t3 - eop
           */
          .test_name = "ProrgamWithBothParserAndIngressControl",
          .control_to_expected_info =
              {
                  {"start", {EndOfParser(), true}},
                  {"parse_ipv4", {EndOfParser(), false}},
                  {"c1", {"t3", true}},
                  {"t1", {"t3", false}},
                  {"t2", {"t3", false}},
                  {"t3", {EndOfPipeline(), true}},
              },
          .ir_program_text_proto = R"pb(
            pipeline {
              key: "ingress"
              value { name: "ingress" initial_control: "c1" }
            }
            parsers {
              key: "parser"
              value {
                name: "parser"
                initial_state: "start"
                parse_states {
                  key: "start"
                  value {
                    name: "start"
                    parser_ops {
                      extract { header { header_name: "ethernet" } }
                    }
                    transition_key_fields {
                      field { header_name: "ethernet" field_name: "ether_type" }
                    }
                    transitions {
                      hex_string_transition {
                        value { value: "0x0800" }
                        mask {}
                        next_state: "parse_ipv4"
                      }
                    }
                    transitions { default_transition { next_state: $eoparser } }
                  }
                }
                parse_states {
                  key: "parse_ipv4"
                  value {
                    name: "parse_ipv4"
                    parser_ops { extract { header { header_name: "ipv4" } } }
                    transitions { default_transition { next_state: $eoparser } }
                  }
                }
              }
            }
            conditionals {
              key: "c1"
              value { name: "c1" if_branch: "t1" else_branch: "t2" }
            }
            tables {
              key: "t1"
              value {
                table_implementation { action_to_next_control { value: "t3" } }
              }
            }
            tables {
              key: "t2"
              value {
                table_implementation { action_to_next_control { value: "t3" } }
              }
            }
            tables {
              key: "t3"
              value {
                table_implementation { action_to_next_control { value: $eop } }
              }
            }
          )pb",
      },
  };
}

constexpr absl::string_view kMinimalProgram = R"pb(
  pipeline {
    key: "ingress"
    value { name: "ingress" initial_control: "c1" }
  }
  parsers {
    key: "parser"
    value {
      name: "parser"
      initial_state: "start"
      parse_states {
        key: "start"
        value {
          name: "start"
          transitions { default_transition { next_state: $eoparser } }
        }
      }
    }
  }
  conditionals {
    key: "c1"
    value { name: "c1" if_branch: "t1" else_branch: "t1" }
  }
  tables {
    key: "t1"
    value { table_implementation { action_to_next_control { value: $eop } } }
  }
)pb";

constexpr absl::string_view kUnknownParseStateProgram = R"pb(
  pipeline {
    key: "ingress"
    value { name: "ingress" initial_control: $eop }
  }
  parsers {
    key: "parser"
    value {
      name: "parser"
      initial_state: "start"
      parse_states {
        key: "start"
        value {
          name: "start"
          parser_ops { extract { header { header_name: "ethernet" } } }
          transitions { default_transition { next_state: "unknown" } }
        }
      }
    }
  }
)pb";

constexpr absl::string_view kNodeConflictProgram = R"pb(
  pipeline {
    key: "ingress"
    value { name: "ingress" initial_control: "start" }
  }
  parsers {
    key: "parser"
    value {
      name: "parser"
      initial_state: "start"
      parse_states {
        key: "start"
        value {
          name: "start"
          parser_ops { extract { header { header_name: "ethernet" } } }
          transitions { default_transition { next_state: $eoparser } }
        }
      }
    }
  }
  tables {
    key: "start"
    value { table_implementation { action_to_next_control { value: $eop } } }
  }
)pb";

TEST(GetOptimizedSymbolicExecutionInfoTest, ReturnsErrorForEndOfPipeline) {
  ASSERT_OK_AND_ASSIGN(const P4Program program,
                       ReplaceEopAndParseProgramTextProto(kMinimalProgram));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<ControlFlowGraph> cfg,
                       ControlFlowGraph::Create(program));

  ASSERT_THAT(cfg->GetOptimizedSymbolicExecutionInfo(EndOfPipeline()),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(GetOptimizedSymbolicExecutionInfoTest, ReturnsErrorForEndOfParser) {
  ASSERT_OK_AND_ASSIGN(const P4Program program,
                       ReplaceEopAndParseProgramTextProto(kMinimalProgram));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<ControlFlowGraph> cfg,
                       ControlFlowGraph::Create(program));

  ASSERT_THAT(cfg->GetOptimizedSymbolicExecutionInfo(EndOfParser()),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(GetOptimizedSymbolicExecutionInfoTest, ReturnsErrorForNonExistingNode) {
  ASSERT_OK_AND_ASSIGN(const P4Program program,
                       ReplaceEopAndParseProgramTextProto(kMinimalProgram));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<ControlFlowGraph> cfg,
                       ControlFlowGraph::Create(program));

  ASSERT_THAT(cfg->GetOptimizedSymbolicExecutionInfo("non_existing_node"),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(GetOptimizedSymbolicExecutionInfoTest, SucceedsForExistingControlNode) {
  ASSERT_OK_AND_ASSIGN(const P4Program program,
                       ReplaceEopAndParseProgramTextProto(kMinimalProgram));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<ControlFlowGraph> cfg,
                       ControlFlowGraph::Create(program));

  ASSERT_THAT(cfg->GetOptimizedSymbolicExecutionInfo("c1"),
              StatusIs(absl::StatusCode::kOk));
}

TEST(GetOptimizedSymbolicExecutionInfoTest, SucceedsForExistingTableNode) {
  ASSERT_OK_AND_ASSIGN(const P4Program program,
                       ReplaceEopAndParseProgramTextProto(kMinimalProgram));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<ControlFlowGraph> cfg,
                       ControlFlowGraph::Create(program));

  ASSERT_THAT(cfg->GetOptimizedSymbolicExecutionInfo("t1"),
              StatusIs(absl::StatusCode::kOk));
}

TEST(GetOptimizedSymbolicExecutionInfoTest, SucceedsForExistingParseState) {
  ASSERT_OK_AND_ASSIGN(const P4Program program,
                       ReplaceEopAndParseProgramTextProto(kMinimalProgram));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<ControlFlowGraph> cfg,
                       ControlFlowGraph::Create(program));

  ASSERT_THAT(cfg->GetOptimizedSymbolicExecutionInfo("start"),
              StatusIs(absl::StatusCode::kOk));
}

TEST(CfgTest, ReturnsErrorForUnknownParseState) {
  ASSERT_OK_AND_ASSIGN(
      const P4Program program,
      ReplaceEopAndParseProgramTextProto(kUnknownParseStateProgram));

  ASSERT_THAT(ControlFlowGraph::Create(program),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       "Unknown parse state: 'unknown'"));
}

TEST(CfgTest, ReturnsErrorForNodeConflict) {
  ASSERT_OK_AND_ASSIGN(
      const P4Program program,
      ReplaceEopAndParseProgramTextProto(kNodeConflictProgram));

  ASSERT_THAT(ControlFlowGraph::Create(program),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       "Nodes of different types have the same name: start"));
}

TEST_P(CfgTest, GetOptimizedSymbolicExecutionInfoReturnsExpectedInfo) {
  const CfgTestParam& param = GetParam();

  ASSERT_OK_AND_ASSIGN(
      const P4Program program,
      ReplaceEopAndParseProgramTextProto(param.ir_program_text_proto));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<ControlFlowGraph> cfg,
                       ControlFlowGraph::Create(program));

  for (const auto& [control_name, expected_output] :
       param.control_to_expected_info) {
    SCOPED_TRACE(absl::StrCat("control node: ", control_name));
    ASSERT_OK_AND_ASSIGN(auto info,
                         cfg->GetOptimizedSymbolicExecutionInfo(control_name));
    EXPECT_EQ(info.merge_point(), expected_output.merge_point);
    EXPECT_EQ(info.continue_to_merge_point(),
              expected_output.continue_to_merge_point);
  }
}

INSTANTIATE_TEST_SUITE_P(
    CfgTests, CfgTest, ValuesIn(GetCfgTestInstances()),
    [](const testing::TestParamInfo<CfgTest::ParamType>& info) {
      return info.param.test_name;
    });

}  // namespace
}  // namespace p4_symbolic::ir

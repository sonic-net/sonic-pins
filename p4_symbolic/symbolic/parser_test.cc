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

#include "p4_symbolic/symbolic/parser.h"

#include <string>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/log/log.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/status_matchers.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/v1model.h"
#include "z3++.h"

namespace p4_symbolic::symbolic::parser {
namespace {

using gutil::StatusIs;

constexpr absl::string_view kErrors = R"pb(
  errors {
    key: "NoError"
    value { name: "NoError" }
  }
  errors {
    key: "PacketTooShort"
    value { name: "PacketTooShort" value: 1 }
  }
  errors {
    key: "NoMatch"
    value { name: "NoMatch" value: 2 }
  }
  errors {
    key: "StackOutOfBounds"
    value { name: "StackOutOfBounds" value: 3 }
  }
  errors {
    key: "HeaderTooShort"
    value { name: "HeaderTooShort" value: 4 }
  }
  errors {
    key: "ParserTimeout"
    value { name: "ParserTimeout" value: 5 }
  }
  errors {
    key: "ParserInvalidArgument"
    value { name: "ParserInvalidArgument" value: 6 }
  }
)pb";

constexpr absl::string_view kHeaders = R"pb(
  headers {
    key: "ethernet"
    value {
      name: "ethernet_t"
      id: 4
      fields {
        key: "dst_addr"
        value { name: "dst_addr" bitwidth: 48 }
      }
      fields {
        key: "ether_type"
        value { name: "ether_type" bitwidth: 16 }
      }
      fields {
        key: "src_addr"
        value { name: "src_addr" bitwidth: 48 }
      }
      ordered_fields_list: "dst_addr"
      ordered_fields_list: "src_addr"
      ordered_fields_list: "ether_type"
    }
  }
  headers {
    key: "ipv4"
    value {
      name: "ipv4_t"
      id: 5
      fields {
        key: "do_not_fragment"
        value { name: "do_not_fragment" bitwidth: 1 }
      }
      fields {
        key: "dscp"
        value { name: "dscp" bitwidth: 6 }
      }
      fields {
        key: "dst_addr"
        value { name: "dst_addr" bitwidth: 32 }
      }
      fields {
        key: "ecn"
        value { name: "ecn" bitwidth: 2 }
      }
      fields {
        key: "frag_offset"
        value { name: "frag_offset" bitwidth: 13 }
      }
      fields {
        key: "header_checksum"
        value { name: "header_checksum" bitwidth: 16 }
      }
      fields {
        key: "identification"
        value { name: "identification" bitwidth: 16 }
      }
      fields {
        key: "ihl"
        value { name: "ihl" bitwidth: 4 }
      }
      fields {
        key: "more_fragments"
        value { name: "more_fragments" bitwidth: 1 }
      }
      fields {
        key: "protocol"
        value { name: "protocol" bitwidth: 8 }
      }
      fields {
        key: "reserved"
        value { name: "reserved" bitwidth: 1 }
      }
      fields {
        key: "src_addr"
        value { name: "src_addr" bitwidth: 32 }
      }
      fields {
        key: "total_len"
        value { name: "total_len" bitwidth: 16 }
      }
      fields {
        key: "ttl"
        value { name: "ttl" bitwidth: 8 }
      }
      fields {
        key: "version"
        value { name: "version" bitwidth: 4 }
      }
      ordered_fields_list: "version"
      ordered_fields_list: "ihl"
      ordered_fields_list: "dscp"
      ordered_fields_list: "ecn"
      ordered_fields_list: "total_len"
      ordered_fields_list: "identification"
      ordered_fields_list: "reserved"
      ordered_fields_list: "do_not_fragment"
      ordered_fields_list: "more_fragments"
      ordered_fields_list: "frag_offset"
      ordered_fields_list: "ttl"
      ordered_fields_list: "protocol"
      ordered_fields_list: "header_checksum"
      ordered_fields_list: "src_addr"
      ordered_fields_list: "dst_addr"
    }
  }
  headers {
    key: "standard_metadata"
    value {
      name: "standard_metadata"
      id: 1
      fields {
        key: "_padding"
        value { name: "_padding" bitwidth: 3 }
      }
      fields {
        key: "checksum_error"
        value { name: "checksum_error" bitwidth: 1 }
      }
      fields {
        key: "deq_qdepth"
        value { name: "deq_qdepth" bitwidth: 19 }
      }
      fields {
        key: "deq_timedelta"
        value { name: "deq_timedelta" bitwidth: 32 }
      }
      fields {
        key: "egress_global_timestamp"
        value { name: "egress_global_timestamp" bitwidth: 48 }
      }
      fields {
        key: "egress_port"
        value { name: "egress_port" bitwidth: 9 }
      }
      fields {
        key: "egress_rid"
        value { name: "egress_rid" bitwidth: 16 }
      }
      fields {
        key: "egress_spec"
        value { name: "egress_spec" bitwidth: 9 }
      }
      fields {
        key: "enq_qdepth"
        value { name: "enq_qdepth" bitwidth: 19 }
      }
      fields {
        key: "enq_timestamp"
        value { name: "enq_timestamp" bitwidth: 32 }
      }
      fields {
        key: "ingress_global_timestamp"
        value { name: "ingress_global_timestamp" bitwidth: 48 }
      }
      fields {
        key: "ingress_port"
        value { name: "ingress_port" bitwidth: 9 }
      }
      fields {
        key: "instance_type"
        value { name: "instance_type" bitwidth: 32 }
      }
      fields {
        key: "mcast_grp"
        value { name: "mcast_grp" bitwidth: 16 }
      }
      fields {
        key: "packet_length"
        value { name: "packet_length" bitwidth: 32 }
      }
      fields {
        key: "parser_error"
        value { name: "parser_error" bitwidth: 32 }
      }
      fields {
        key: "priority"
        value { name: "priority" bitwidth: 3 }
      }
      ordered_fields_list: "ingress_port"
      ordered_fields_list: "egress_spec"
      ordered_fields_list: "egress_port"
      ordered_fields_list: "instance_type"
      ordered_fields_list: "packet_length"
      ordered_fields_list: "enq_timestamp"
      ordered_fields_list: "enq_qdepth"
      ordered_fields_list: "deq_timedelta"
      ordered_fields_list: "deq_qdepth"
      ordered_fields_list: "ingress_global_timestamp"
      ordered_fields_list: "egress_global_timestamp"
      ordered_fields_list: "mcast_grp"
      ordered_fields_list: "egress_rid"
      ordered_fields_list: "checksum_error"
      ordered_fields_list: "parser_error"
      ordered_fields_list: "priority"
      ordered_fields_list: "_padding"
    }
  }
)pb";

absl::StatusOr<ir::Dataplane> ParseProgramTextProto(
    absl::string_view ir_program_text_proto) {
  ASSIGN_OR_RETURN(
      ir::P4Program program,
      gutil::ParseTextProto<ir::P4Program>(absl::StrCat(
          kErrors, kHeaders,
          absl::StrReplaceAll(
              ir_program_text_proto,
              {
                  {"$eoparser", absl::Substitute("\"$0\"", ir::EndOfParser())},
                  {"$eop", absl::Substitute("\"$0\"", ir::EndOfPipeline())},
              }))));
  return ir::Dataplane{std::move(program)};
}

constexpr absl::string_view kProgramWithTwoParsers = R"pb(
  parsers {
    key: "parser1"
    value {
      name: "parser1"
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
  parsers {
    key: "parser2"
    value {
      name: "parser2"
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
)pb";

TEST(EvaluateParsers, ReturnsErrorForMoreThanOneParser) {
  ASSERT_OK_AND_ASSIGN(const ir::Dataplane data_plane,
                       ParseProgramTextProto(kProgramWithTwoParsers));
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  EXPECT_THAT(EvaluateParsers(data_plane.program, ingress_headers, z3_context),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       "Invalid number of parsers: 2"));
}

TEST(EvaluateParsers, ReturnsErrorForLessThanOneParser) {
  ASSERT_OK_AND_ASSIGN(const ir::Dataplane data_plane,
                       ParseProgramTextProto(""));
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  EXPECT_THAT(EvaluateParsers(data_plane.program, ingress_headers, z3_context),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       "Invalid number of parsers: 0"));
}

constexpr absl::string_view kProgramWithUnknownParseState = R"pb(
  parsers {
    key: "parser"
    value {
      name: "parser"
      initial_state: "start"
      parse_states {
        key: "start"
        value {
          name: "start"
          transitions { default_transition { next_state: "unknown" } }
        }
      }
    }
  }
)pb";

TEST(EvaluateParsers, ReturnsErrorForUnknownParseState) {
  ASSERT_OK_AND_ASSIGN(const ir::Dataplane data_plane,
                       ParseProgramTextProto(kProgramWithUnknownParseState));
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  EXPECT_THAT(
      EvaluateParsers(data_plane.program, ingress_headers, z3_context),
      StatusIs(absl::StatusCode::kNotFound, "Parse state not found: unknown"));
}

constexpr absl::string_view kProgramWithUnknownHeaderExtract = R"pb(
  parsers {
    key: "parser"
    value {
      name: "parser"
      initial_state: "start"
      parse_states {
        key: "start"
        value {
          name: "start"
          parser_ops { extract { header { header_name: "unknown" } } }
          transitions { default_transition { next_state: $eoparser } }
        }
      }
    }
  }
)pb";

TEST(EvaluateParsers, ReturnsErrorForUnknownHeaderExtract) {
  ASSERT_OK_AND_ASSIGN(const ir::Dataplane data_plane,
                       ParseProgramTextProto(kProgramWithUnknownHeaderExtract));
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  EXPECT_THAT(
      EvaluateParsers(data_plane.program, ingress_headers, z3_context),
      StatusIs(absl::StatusCode::kNotFound, "Header not found: unknown"));
}

constexpr absl::string_view kProgramExtractEthernet = R"pb(
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
)pb";

TEST(EvaluateParsers, ReturnsErrorForNonFreeBitVectorHeaderField) {
  ASSERT_OK_AND_ASSIGN(const ir::Dataplane data_plane,
                       ParseProgramTextProto(kProgramExtractEthernet));
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  ASSERT_OK(ingress_headers.Set("ethernet.dst_addr", z3_context.bv_val(0, 48),
                                z3_context.bool_val(true)));
  EXPECT_THAT(
      EvaluateParsers(data_plane.program, ingress_headers, z3_context),
      StatusIs(absl::StatusCode::kInvalidArgument,
               testing::StartsWith(
                   "Field 'ethernet.dst_addr' should be a free bit-vector. "
                   "Found: ")));
}

constexpr absl::string_view kProgramWithUnknownFieldSet = R"pb(
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
            set {
              lvalue { header_name: "ethernet" field_name: "unknown" }
              hexstr_rvalue { value: "0xBEEF" }
            }
          }
          transitions { default_transition { next_state: $eoparser } }
        }
      }
    }
  }
)pb";

TEST(EvaluateParsers, ReturnsErrorForUnknownFieldSet) {
  ASSERT_OK_AND_ASSIGN(const ir::Dataplane data_plane,
                       ParseProgramTextProto(kProgramWithUnknownFieldSet));
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  EXPECT_THAT(
      EvaluateParsers(data_plane.program, ingress_headers, z3_context),
      StatusIs(
          absl::StatusCode::kInvalidArgument,
          "Cannot assign to key \"ethernet.unknown\" in SymbolicGuardedMap!"));
}

constexpr absl::string_view kProgramWithLookaheadSet = R"pb(
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
            set {
              lvalue { header_name: "ethernet" field_name: "dst_addr" }
              lookahead_rvalue { bitwidth: 48 }
            }
          }
          transitions { default_transition { next_state: $eoparser } }
        }
      }
    }
  }
)pb";

TEST(EvaluateParsers, ReturnsErrorForUnimplementedLookaheadSet) {
  ASSERT_OK_AND_ASSIGN(const ir::Dataplane data_plane,
                       ParseProgramTextProto(kProgramWithLookaheadSet));
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  EXPECT_THAT(
      EvaluateParsers(data_plane.program, ingress_headers, z3_context),
      StatusIs(absl::StatusCode::kUnimplemented,
               "Lookahead R-values for set operations are not supported."));
}

constexpr absl::string_view kProgramWithNonHeaderFieldTransitionKey = R"pb(
  parsers {
    key: "parser"
    value {
      name: "parser"
      initial_state: "start"
      parse_states {
        key: "start"
        value {
          name: "start"
          transition_key_fields { lookahead { bitwidth: 16 } }
          transitions { default_transition { next_state: $eoparser } }
        }
      }
    }
  }
)pb";

TEST(EvaluateParsers, ReturnsErrorForNonHeaderFieldTransitionKey) {
  ASSERT_OK_AND_ASSIGN(
      const ir::Dataplane data_plane,
      ParseProgramTextProto(kProgramWithNonHeaderFieldTransitionKey));
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  EXPECT_THAT(EvaluateParsers(data_plane.program, ingress_headers, z3_context),
              StatusIs(absl::StatusCode::kUnimplemented));
}

constexpr absl::string_view kProgramWithUnknownFieldTransitionKey = R"pb(
  parsers {
    key: "parser"
    value {
      name: "parser"
      initial_state: "start"
      parse_states {
        key: "start"
        value {
          name: "start"
          transition_key_fields {
            field { header_name: "un" field_name: "known" }
          }
          transitions { default_transition { next_state: $eoparser } }
        }
      }
    }
  }
)pb";

TEST(EvaluateParsers, ReturnsErrorForUnknownFieldTransitionKey) {
  ASSERT_OK_AND_ASSIGN(
      const ir::Dataplane data_plane,
      ParseProgramTextProto(kProgramWithUnknownFieldTransitionKey));
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  EXPECT_THAT(EvaluateParsers(data_plane.program, ingress_headers, z3_context),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       "Cannot find key \"un.known\" in SymbolicGuardedMap!"));
}

constexpr absl::string_view kProgramWithDeadCodeTransition = R"pb(
  parsers {
    key: "parser"
    value {
      name: "parser"
      initial_state: "start"
      parse_states {
        key: "start"
        value {
          name: "start"
          transition_key_fields {
            field { header_name: "ethernet" field_name: "ether_type" }
          }
          transitions {
            hex_string_transition {
              value { value: "0x0000" }
              mask { value: "0xfe00" }
              next_state: $eoparser
            }
          }
          transitions { default_transition { next_state: $eoparser } }
          transitions {
            hex_string_transition {
              value { value: "0x0800" }
              mask {}
              next_state: "parse_ipv4"
            }
          }
        }
      }
    }
  }
)pb";

TEST(EvaluateParsers, ReturnsErrorForDeadCodeTransition) {
  ASSERT_OK_AND_ASSIGN(const ir::Dataplane data_plane,
                       ParseProgramTextProto(kProgramWithDeadCodeTransition));
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  EXPECT_THAT(EvaluateParsers(data_plane.program, ingress_headers, z3_context),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

constexpr absl::string_view kProgramWithNoTransitionKey = R"pb(
  parsers {
    key: "parser"
    value {
      name: "parser"
      initial_state: "start"
      parse_states {
        key: "start"
        value {
          name: "start"
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
)pb";

TEST(EvaluateParsers, ReturnsErrorForNoTransitionKey) {
  ASSERT_OK_AND_ASSIGN(const ir::Dataplane data_plane,
                       ParseProgramTextProto(kProgramWithNoTransitionKey));
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  EXPECT_THAT(
      EvaluateParsers(data_plane.program, ingress_headers, z3_context),
      StatusIs(
          absl::StatusCode::kNotFound,
          "No transition key specified but hex string transitions exist."));
}

struct ParserTestParam {
  // Text proto representing the input IR P4Program.
  std::string ir_program_text_proto;
  // Expected SMT formulae of the parsed headers keyed with fully qualified
  // header field names. If a header field is not specified in this map, its
  // symbolic value remains untouched, meaning that it will be the same as that
  // of the ingress headers. Note that the symbolic expressions of all header
  // fields are checked against the parsed headers rather than just the
  // specified ones.
  std::function<absl::btree_map<std::string, z3::expr>(z3::context&)>
      expected_symbolic_parsed_headers;
};

using EvaluateParsersTest = ::testing::TestWithParam<ParserTestParam>;

std::vector<ParserTestParam> GetParserTestInstances() {
  return {
      {
          // Minimal parser. The parsed headers should be the same as the
          // ingress headers.
          .ir_program_text_proto = R"pb(
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
                    optimized_symbolic_execution_info {
                      merge_point: $eoparser
                      continue_to_merge_point: true
                    }
                  }
                }
              }
            }
          )pb",
          .expected_symbolic_parsed_headers = [](z3::context& ctx)
              -> absl::btree_map<std::string, z3::expr> { return {}; },
      },
      {
          // Basic parser with Ethernet and IPv4 headers.
          .ir_program_text_proto = R"pb(
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
                    optimized_symbolic_execution_info {
                      merge_point: $eoparser
                      continue_to_merge_point: true
                    }
                  }
                }
                parse_states {
                  key: "parse_ipv4"
                  value {
                    name: "parse_ipv4"
                    parser_ops { extract { header { header_name: "ipv4" } } }
                    transitions { default_transition { next_state: $eoparser } }
                    optimized_symbolic_execution_info { merge_point: $eoparser }
                  }
                }
              }
            }
          )pb",
          .expected_symbolic_parsed_headers =
              [](z3::context& ctx) -> absl::btree_map<std::string, z3::expr> {
            return {
                {"ethernet.$valid$", ctx.bool_val(true)},
                {"ethernet.$extracted$", ctx.bool_val(true)},
                {"ipv4.$valid$", (ctx.bv_const("ethernet.ether_type", 16) ==
                                  ctx.bv_val(0x0800, 16))},
                {"ipv4.$extracted$", (ctx.bv_const("ethernet.ether_type", 16) ==
                                      ctx.bv_val(0x0800, 16))},
            };
          },
      },
      {
          // Parser with set operations.
          .ir_program_text_proto = R"pb(
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
                    parser_ops {
                      set {
                        lvalue {
                          header_name: "ethernet"
                          field_name: "dst_addr"
                        }
                        hexstr_rvalue { value: "0x0000DEADBEEF" }
                      }
                    }
                    parser_ops {
                      set {
                        lvalue {
                          header_name: "ethernet"
                          field_name: "src_addr"
                        }
                        field_rvalue {
                          header_name: "ethernet"
                          field_name: "dst_addr"
                        }
                      }
                    }
                    parser_ops {
                      set {
                        lvalue {
                          header_name: "ethernet"
                          field_name: "src_addr"
                        }
                        expression_rvalue {
                          binary_expression {
                            operation: BIT_AND
                            left {
                              field_value {
                                header_name: "ethernet"
                                field_name: "src_addr"
                              }
                            }
                            right { hexstr_value { value: "0x00000000FFFF" } }
                          }
                        }
                      }
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
                    optimized_symbolic_execution_info {
                      merge_point: $eoparser
                      continue_to_merge_point: true
                    }
                  }
                }
                parse_states {
                  key: "parse_ipv4"
                  value {
                    name: "parse_ipv4"
                    parser_ops { extract { header { header_name: "ipv4" } } }
                    transitions { default_transition { next_state: $eoparser } }
                    optimized_symbolic_execution_info { merge_point: $eoparser }
                  }
                }
              }
            }
          )pb",
          .expected_symbolic_parsed_headers =
              [](z3::context& ctx) -> absl::btree_map<std::string, z3::expr> {
            return {
                {"ethernet.$valid$", ctx.bool_val(true)},
                {"ethernet.$extracted$", ctx.bool_val(true)},
                {"ethernet.dst_addr", ctx.bv_val(0xDEADBEEF, 48)},
                {"ethernet.src_addr", ctx.bv_val(0xBEEF, 48)},
                {"ipv4.$valid$", (ctx.bv_const("ethernet.ether_type", 16) ==
                                  ctx.bv_val(0x0800, 16))},
                {"ipv4.$extracted$", (ctx.bv_const("ethernet.ether_type", 16) ==
                                      ctx.bv_val(0x0800, 16))},
            };
          },
      },
      {
          // Parser with primitive operations.
          .ir_program_text_proto = R"pb(
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
                    parser_ops {
                      primitive {
                        assignment {
                          left {
                            field_value {
                              header_name: "ethernet"
                              field_name: "$valid$"
                            }
                          }
                          right { bool_value { value: true } }
                        }
                      }
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
                    optimized_symbolic_execution_info {
                      merge_point: $eoparser
                      continue_to_merge_point: true
                    }
                  }
                }
                parse_states {
                  key: "parse_ipv4"
                  value {
                    name: "parse_ipv4"
                    parser_ops { extract { header { header_name: "ipv4" } } }
                    parser_ops {
                      primitive {
                        assignment {
                          left {
                            field_value {
                              header_name: "ethernet"
                              field_name: "$valid$"
                            }
                          }
                          right { bool_value {} }
                        }
                      }
                    }
                    transitions { default_transition { next_state: $eoparser } }
                    optimized_symbolic_execution_info { merge_point: $eoparser }
                  }
                }
              }
            }
          )pb",
          .expected_symbolic_parsed_headers =
              [](z3::context& ctx) -> absl::btree_map<std::string, z3::expr> {
            return {
                {"ethernet.$valid$", (ctx.bv_const("ethernet.ether_type", 16) !=
                                      ctx.bv_val(0x0800, 16))},
                {"ethernet.$extracted$", ctx.bool_val(true)},
                {"ipv4.$valid$", (ctx.bv_const("ethernet.ether_type", 16) ==
                                  ctx.bv_val(0x0800, 16))},
                {"ipv4.$extracted$", (ctx.bv_const("ethernet.ether_type", 16) ==
                                      ctx.bv_val(0x0800, 16))},
            };
          },
      },
      {
          // Parser with masked hex string transitions.
          .ir_program_text_proto = R"pb(
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
                        mask { value: "0xff00" }
                        next_state: "parse_ipv4"
                      }
                    }
                    transitions { default_transition { next_state: $eoparser } }
                    optimized_symbolic_execution_info {
                      merge_point: $eoparser
                      continue_to_merge_point: true
                    }
                  }
                }
                parse_states {
                  key: "parse_ipv4"
                  value {
                    name: "parse_ipv4"
                    parser_ops { extract { header { header_name: "ipv4" } } }
                    transitions { default_transition { next_state: $eoparser } }
                    optimized_symbolic_execution_info { merge_point: $eoparser }
                  }
                }
              }
            }
          )pb",
          .expected_symbolic_parsed_headers =
              [](z3::context& ctx) -> absl::btree_map<std::string, z3::expr> {
            return {
                {"ethernet.$valid$", ctx.bool_val(true)},
                {"ethernet.$extracted$", ctx.bool_val(true)},
                {"ipv4.$valid$",
                 ((ctx.bv_const("ethernet.ether_type", 16) &
                   ctx.bv_val(0xff00, 16)) == ctx.bv_val(0x0800, 16))},
                {"ipv4.$extracted$",
                 ((ctx.bv_const("ethernet.ether_type", 16) &
                   ctx.bv_val(0xff00, 16)) == ctx.bv_val(0x0800, 16))},
            };
          },
      },
      {
          // Parser with fall-through (error.NoMatch) conditions.
          .ir_program_text_proto = R"pb(
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
                    optimized_symbolic_execution_info {
                      merge_point: "parse_ipv4"
                      continue_to_merge_point: true
                    }
                  }
                }
                parse_states {
                  key: "parse_ipv4"
                  value {
                    name: "parse_ipv4"
                    parser_ops { extract { header { header_name: "ipv4" } } }
                    transitions { default_transition { next_state: $eoparser } }
                    optimized_symbolic_execution_info {
                      merge_point: $eoparser
                      continue_to_merge_point: true
                    }
                  }
                }
              }
            }
          )pb",
          .expected_symbolic_parsed_headers =
              [](z3::context& ctx) -> absl::btree_map<std::string, z3::expr> {
            return {
                {"ethernet.$valid$", ctx.bool_val(true)},
                {"ethernet.$extracted$", ctx.bool_val(true)},
                {"ipv4.$valid$", (ctx.bv_const("ethernet.ether_type", 16) ==
                                  ctx.bv_val(0x0800, 16))},
                {"ipv4.$extracted$", (ctx.bv_const("ethernet.ether_type", 16) ==
                                      ctx.bv_val(0x0800, 16))},
                {std::string(v1model::kParserErrorField),
                 z3::ite((ctx.bv_const("ethernet.ether_type", 16) !=
                          ctx.bv_val(0x0800, 16)),
                         ctx.bv_val(2, 32), ctx.bv_val(0, 32))},
            };
          },
      },
  };
}

TEST_P(EvaluateParsersTest, ValidateParsedHeadersSMTFormulae) {
  z3::context z3_context;

  // Parse the P4 program from IR text proto and evaluate the parsers.
  const ParserTestParam& param = GetParam();
  ASSERT_OK_AND_ASSIGN(const ir::Dataplane data_plane,
                       ParseProgramTextProto(param.ir_program_text_proto));
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  ASSERT_OK(v1model::InitializeIngressHeaders(data_plane.program,
                                              ingress_headers, z3_context));
  ASSERT_OK_AND_ASSIGN(
      SymbolicPerPacketState parsed_headers,
      EvaluateParsers(data_plane.program, ingress_headers, z3_context));

  // Construct the expected parsed headers.
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState expected_parsed_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           z3_context, data_plane.program.headers()));
  ASSERT_OK(v1model::InitializeIngressHeaders(
      data_plane.program, expected_parsed_headers, z3_context));
  // Update the expected SMT formulae of certain fields specified by the test.
  for (const auto& [field_name, field] :
       param.expected_symbolic_parsed_headers(z3_context)) {
    ASSERT_TRUE(expected_parsed_headers.ContainsKey(field_name));
    ASSERT_OK(expected_parsed_headers.UnguardedSet(field_name, field));
  }

  auto solver = std::make_unique<z3::solver>(z3_context);

  // Check if the SMT formulae of the parsed headers are semantically the
  // same as the expected parsed headers.
  for (const auto& [field_name, actual_value] : parsed_headers) {
    ASSERT_TRUE(expected_parsed_headers.ContainsKey(field_name));
    ASSERT_OK_AND_ASSIGN(z3::expr expected_value,
                         expected_parsed_headers.Get(field_name));
    LOG(INFO) << "Check semantic equivalence for " << field_name << ": "
              << expected_value << " vs " << actual_value;
    z3::expr_vector assumptions(z3_context);
    assumptions.push_back(expected_value != actual_value);
    EXPECT_EQ(solver->check(assumptions), z3::check_result::unsat);
  }
}

INSTANTIATE_TEST_SUITE_P(EvaluateParsers, EvaluateParsersTest,
                         ::testing::ValuesIn(GetParserTestInstances()));

}  // namespace
}  // namespace p4_symbolic::symbolic::parser

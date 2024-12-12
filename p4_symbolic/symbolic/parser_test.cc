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
#include "absl/strings/str_replace.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/status_matchers.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/v1model.h"
#include "p4_symbolic/z3_util.h"
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
    }
  }
  headers {
    key: "standard_metadata"
    value {
      name: "standard_metadata"
      id: 1
      fields {
        key: "parser_error"
        value { name: "parser_error" bitwidth: 32 }
      }
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
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           data_plane.program.headers()));
  EXPECT_THAT(EvaluateParsers(data_plane.program, ingress_headers),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       "Invalid number of parsers: 2"));
}

TEST(EvaluateParsers, ReturnsErrorForLessThanOneParser) {
  ASSERT_OK_AND_ASSIGN(const ir::Dataplane data_plane,
                       ParseProgramTextProto(""));
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           data_plane.program.headers()));
  EXPECT_THAT(EvaluateParsers(data_plane.program, ingress_headers),
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
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           data_plane.program.headers()));
  EXPECT_THAT(
      EvaluateParsers(data_plane.program, ingress_headers),
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
  ASSERT_OK_AND_ASSIGN(SymbolicPerPacketState ingress_headers,
                       SymbolicGuardedMap::CreateSymbolicGuardedMap(
                           data_plane.program.headers()));
  EXPECT_THAT(
      EvaluateParsers(data_plane.program, ingress_headers),
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

}  // namespace
}  // namespace p4_symbolic::symbolic::parser

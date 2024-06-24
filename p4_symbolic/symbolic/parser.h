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

// Hardcodes the behavior of an interesting p4 parser that is part
// of the p4 program we are interested in.
// The hardcoded behavior sets the validity of certain header fields
// based on the fields in the packet, and sets the default values
// for local_metadata fields.

#ifndef P4_SYMBOLIC_SYMBOLIC_PARSER_H_
#define P4_SYMBOLIC_SYMBOLIC_PARSER_H_

#include <vector>

#include "gutil/status.h"
#include "p4_symbolic/symbolic/symbolic.h"

#define ETHERTYPE_IPV4 0x0800
#define ETHERTYPE_IPV6 0x86dd
#define ETHERTYPE_ARP 0x0806

#define IP_PROTOCOL_TCP 0x06
#define IP_PROTOCOL_UDP 0x11
#define IP_PROTOCOL_ICMP 0x01
#define IP_PROTOCOL_ICMPV6 0x3a

namespace p4_symbolic {
namespace symbolic {
namespace parser {

// Creates assertions/constraints that encode some of the interesting
// behavior of parsers in specific programs we want to analyze.
absl::StatusOr<std::vector<z3::expr>> EvaluateHardcodedParser(
    const SymbolicPerPacketState &state);

}  // namespace parser
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_PARSER_H_

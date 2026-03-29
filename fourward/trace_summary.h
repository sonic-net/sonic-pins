// Human-readable summary of a 4ward trace, focused on debugging.
//
// Extracts the information that matters: table hits/misses, drops with their
// causal conditions, and the packet's final fate. Filters out noise (parser
// transitions, action executions) unless they're relevant.

#ifndef PINS_FOURWARD_TRACE_SUMMARY_H_
#define PINS_FOURWARD_TRACE_SUMMARY_H_

#include <string>

#include "simulator.pb.h"

namespace dvaas {

// Returns a concise human-readable summary of a trace tree, e.g.:
//
//   Tables:
//     disable_vlan_checks_table: HIT
//     l3_admit_table: HIT
//     vrf_table: HIT
//     ipv4_table: MISS → NoAction
//   Drops:
//     mark_to_drop at vlan.p4:129 (condition: enable_vlan_checks && ...)
//   Fate: DROPPED
//
std::string SummarizeTrace(const fourward::sim::TraceTree& trace);

}  // namespace dvaas

#endif  // PINS_FOURWARD_TRACE_SUMMARY_H_

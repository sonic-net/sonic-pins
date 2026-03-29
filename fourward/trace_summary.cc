#include "fourward/trace_summary.h"

#include <string>
#include <vector>

#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "simulator.pb.h"

namespace dvaas {
namespace {

struct TableResult {
  std::string name;
  bool hit;
  std::string action;
};

struct DropEvent {
  std::string location;
  std::string condition;
};

void CollectEvents(const fourward::sim::TraceTree& tree,
                   std::vector<TableResult>& tables,
                   std::vector<DropEvent>& drops,
                   std::string& last_branch_condition,
                   std::string& fate) {
  for (const fourward::sim::TraceEvent& event : tree.events()) {
    switch (event.event_case()) {
      case fourward::sim::TraceEvent::kTableLookup: {
        TableResult result;
        result.name = event.table_lookup().table_name();
        result.hit = event.table_lookup().hit();
        result.action = event.table_lookup().action_name();
        tables.push_back(result);
        break;
      }
      case fourward::sim::TraceEvent::kBranch: {
        std::string taken_str =
            event.branch().taken() ? "true" : "false";
        last_branch_condition = absl::StrCat(
            event.source_info().source_fragment(), " [", taken_str, "]");
        break;
      }
      case fourward::sim::TraceEvent::kMarkToDrop: {
        DropEvent drop;
        if (event.has_source_info()) {
          drop.location = absl::StrCat(
              event.source_info().file(), ":", event.source_info().line());
        }
        drop.condition = last_branch_condition;
        drops.push_back(drop);
        break;
      }
      default:
        break;
    }
  }

  switch (tree.outcome_case()) {
    case fourward::sim::TraceTree::kPacketOutcome:
      switch (tree.packet_outcome().outcome_case()) {
        case fourward::sim::PacketOutcome::kDrop:
          fate = "DROPPED";
          break;
        case fourward::sim::PacketOutcome::kOutput:
          fate = absl::StrCat(
              "OUTPUT on port ",
              tree.packet_outcome().output().p4rt_egress_port().empty()
                  ? absl::StrCat(
                        tree.packet_outcome().output().dataplane_egress_port())
                  : std::string(
                        tree.packet_outcome().output().p4rt_egress_port()));
          break;
        default:
          fate = "UNKNOWN";
          break;
      }
      break;
    case fourward::sim::TraceTree::kForkOutcome:
      for (const fourward::sim::ForkBranch& branch :
           tree.fork_outcome().branches()) {
        CollectEvents(branch.subtree(), tables, drops, last_branch_condition,
                      fate);
      }
      break;
    default:
      break;
  }
}

}  // namespace

std::string SummarizeTrace(const fourward::sim::TraceTree& trace) {
  std::vector<TableResult> tables;
  std::vector<DropEvent> drops;
  std::string last_branch_condition;
  std::string fate;
  CollectEvents(trace, tables, drops, last_branch_condition, fate);

  std::string result;
  absl::StrAppend(&result, "Tables:\n");
  for (const TableResult& table : tables) {
    absl::StrAppend(&result, "  ", table.name, ": ",
                    table.hit ? "HIT" : "MISS");
    if (!table.action.empty()) {
      absl::StrAppend(&result, " → ", table.action);
    }
    absl::StrAppend(&result, "\n");
  }

  if (!drops.empty()) {
    absl::StrAppend(&result, "Drops:\n");
    for (const DropEvent& drop : drops) {
      absl::StrAppend(&result, "  mark_to_drop");
      if (!drop.location.empty()) {
        absl::StrAppend(&result, " at ", drop.location);
      }
      if (!drop.condition.empty()) {
        absl::StrAppend(&result, "\n    after: ", drop.condition);
      }
      absl::StrAppend(&result, "\n");
    }
  }

  absl::StrAppend(&result, "Fate: ", fate.empty() ? "UNKNOWN" : fate, "\n");
  return result;
}

}  // namespace dvaas

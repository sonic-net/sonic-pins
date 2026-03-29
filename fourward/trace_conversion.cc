#include "fourward/trace_conversion.h"

#include <string>

#include "dvaas/packet_trace.pb.h"
#include "simulator.pb.h"

namespace dvaas {
namespace {

void FlattenTraceTree(const fourward::sim::TraceTree& tree,
                      PacketTrace& trace);

void AppendTraceEvent(const fourward::sim::TraceEvent& event,
                      PacketTrace& trace) {
  switch (event.event_case()) {
    case fourward::sim::TraceEvent::kTableLookup: {
      const fourward::sim::TableLookupEvent& lookup = event.table_lookup();
      TableApply& table_apply = *trace.add_events()->mutable_table_apply();
      table_apply.set_table_name(lookup.table_name());
      if (lookup.hit()) {
        table_apply.mutable_hit();
        // TODO: Convert PI TableEntry to PDPI IrTableEntry for
        // table_apply.hit().table_entry(). Wire up when integrating into
        // the DVaaS frontend, which has PDPI available.
      } else {
        table_apply.mutable_miss();
      }
      break;
    }
    case fourward::sim::TraceEvent::kMarkToDrop: {
      MarkToDrop& mark_to_drop =
          *trace.add_events()->mutable_mark_to_drop();
      if (event.has_source_info()) {
        mark_to_drop.set_source_location(
            event.source_info().source_fragment());
      }
      break;
    }
    case fourward::sim::TraceEvent::kClone: {
      PacketReplication& replication =
          *trace.add_events()->mutable_packet_replication();
      replication.set_number_of_packets_replicated(1);
      break;
    }
    case fourward::sim::TraceEvent::kParserTransition:
    case fourward::sim::TraceEvent::kActionExecution:
    case fourward::sim::TraceEvent::kBranch:
    case fourward::sim::TraceEvent::kExternCall:
    case fourward::sim::TraceEvent::kPacketIngress:
    case fourward::sim::TraceEvent::kPipelineStage:
    case fourward::sim::TraceEvent::kCloneSessionLookup:
    case fourward::sim::TraceEvent::kLogMessage:
    case fourward::sim::TraceEvent::kAssertion:
    case fourward::sim::TraceEvent::kDeparserEmit:
    case fourward::sim::TraceEvent::EVENT_NOT_SET:
      break;
  }
}

void AppendOutcome(const fourward::sim::TraceTree& tree,
                   PacketTrace& trace) {
  switch (tree.outcome_case()) {
    case fourward::sim::TraceTree::kForkOutcome: {
      const fourward::sim::Fork& fork = tree.fork_outcome();
      switch (fork.reason()) {
        case fourward::sim::CLONE:
        case fourward::sim::MULTICAST:
        case fourward::sim::RESUBMIT:
        case fourward::sim::RECIRCULATE: {
          // Parallel fork: all branches execute.
          if (fork.reason() == fourward::sim::MULTICAST) {
            PacketReplication& replication =
                *trace.add_events()->mutable_packet_replication();
            replication.set_number_of_packets_replicated(
                fork.branches_size());
          }
          for (const fourward::sim::ForkBranch& branch : fork.branches()) {
            FlattenTraceTree(branch.subtree(), trace);
          }
          break;
        }
        case fourward::sim::ACTION_SELECTOR: {
          // Alternative fork: follow the first branch.
          if (!fork.branches().empty()) {
            FlattenTraceTree(fork.branches(0).subtree(), trace);
          }
          break;
        }
        case fourward::sim::FORK_REASON_UNSPECIFIED:
        default:
          break;
      }
      break;
    }
    case fourward::sim::TraceTree::kPacketOutcome: {
      const fourward::sim::PacketOutcome& outcome = tree.packet_outcome();
      switch (outcome.outcome_case()) {
        case fourward::sim::PacketOutcome::kDrop:
          trace.add_events()->mutable_drop();
          break;
        case fourward::sim::PacketOutcome::kOutput: {
          Transmit& transmit = *trace.add_events()->mutable_transmit();
          transmit.set_port(
              std::string(outcome.output().p4rt_egress_port()));
          transmit.set_packet_size(outcome.output().payload().size());
          break;
        }
        case fourward::sim::PacketOutcome::OUTCOME_NOT_SET:
          break;
      }
      break;
    }
    case fourward::sim::TraceTree::OUTCOME_NOT_SET:
      break;
  }
}

void FlattenTraceTree(const fourward::sim::TraceTree& tree,
                      PacketTrace& trace) {
  for (const fourward::sim::TraceEvent& event : tree.events()) {
    AppendTraceEvent(event, trace);
  }
  AppendOutcome(tree, trace);
}

}  // namespace

PacketTrace FourwardTraceTreeToDvaasPacketTrace(
    const fourward::sim::TraceTree& trace_tree) {
  PacketTrace trace;
  FlattenTraceTree(trace_tree, trace);
  return trace;
}

}  // namespace dvaas

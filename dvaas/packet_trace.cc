#include "dvaas/packet_trace.h"

#include <string>
#include <string_view>

#include "absl/algorithm/container.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_replace.h"
#include "dvaas/test_vector.h"
#include "p4_pdpi/ir.pb.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/test_artifact_writer.h"

namespace dvaas {

dvaas::PacketTrace MakeCompactPacketTrace(dvaas::PacketTrace packet_trace) {
  packet_trace.clear_bmv2_textual_log();
  for (auto& event : *packet_trace.mutable_events()) {
    if (event.has_table_apply()) {
      auto& table_apply = *event.mutable_table_apply();
      if (table_apply.has_miss() || table_apply.hit().has_table_entry())
        table_apply.clear_hit_or_miss_textual_log();
    }
  }
  return packet_trace;
}

std::string GetPacketTraceSummary(const dvaas::PacketTrace& packet_trace) {
  std::string summarized_packet_trace;

  auto indent = [](std::string_view text) {
    return absl::StrReplaceAll(text, {{"\n", "\n  "}});
  };

  for (const dvaas::Event& event : packet_trace.events()) {
    switch (event.event_case()) {
      case Event::kTableApply: {
        if (event.table_apply().hit().has_table_entry()) {
          absl::StrAppend(&summarized_packet_trace, "Table '",
                          event.table_apply().table_name(), "': hit\n  ",
                          indent(gutil::PrintTextProto(
                              event.table_apply().hit().table_entry())),
                          "\n");
        } else if (event.table_apply().has_miss()) {
          absl::StrAppend(&summarized_packet_trace, "Table '",
                          event.table_apply().table_name(), "': miss\n\n");
        } else {
          absl::StrAppend(&summarized_packet_trace,
                          indent(event.table_apply().hit_or_miss_textual_log()),
                          "\n\n");
        }
        break;
      }
      case Event::kMarkToDrop: {
        absl::StrAppend(&summarized_packet_trace, "Primitive: 'mark_to_drop' (",
                        event.mark_to_drop().source_location(), ")\n\n");
        break;
      }
      case Event::kPacketReplication: {
        absl::StrAppend(
            &summarized_packet_trace, "Packet replication: ",
            event.packet_replication().number_of_packets_replicated(),
            " replicas");
        if (event.packet_replication().has_packet_replication_engine_entry()) {
          absl::StrAppend(&summarized_packet_trace, " from hit:\n  ",
                          indent(gutil::PrintTextProto(
                              event.packet_replication()
                                  .packet_replication_engine_entry())));
        }
        absl::StrAppend(&summarized_packet_trace, "\n");
        break;
      }
      case Event::kDrop: {
        absl::StrAppend(&summarized_packet_trace,
                        "Dropping packet at the end of ",
                        event.drop().pipeline(), "\n");
        break;
      }
      case Event::kTransmit: {
        absl::StrAppend(&summarized_packet_trace,
                        "Transmitting packet of size ",
                        event.transmit().packet_size(), " out of port ",
                        event.transmit().port(), "\n");
        break;
      }
      default: {
        LOG(WARNING) << "Event " << event.ShortDebugString()
                     << " not supported.";
        break;
      }
    }
  }
  if (summarized_packet_trace.empty()) {
    summarized_packet_trace = "Packet trace is empty (has no events).\n";
  }
  return summarized_packet_trace;
}

absl::Status StorePacketTraceTextualBmv2LogAsTestArtifact(
    PacketTestOutcome& test_outcome,
    gutil::TestArtifactWriter& dvaas_test_artifact_writer) {
  if (test_outcome.test_result().has_failure()) {
    const auto& acceptable_outputs =
        test_outcome.test_run().test_vector().acceptable_outputs();
    auto full_packet_trace_it =
        absl::c_find_if(acceptable_outputs, [](const auto& output) {
          return output.has_packet_trace() &&
                 !output.packet_trace().bmv2_textual_log().empty();
        });
    if (full_packet_trace_it == acceptable_outputs.end()) {
      return absl::InvalidArgumentError(
          absl::StrCat("No packet trace found in acceptable outputs in ",
                       test_outcome.ShortDebugString()));
    }
    std::string filename;
    ASSIGN_OR_RETURN(
        int test_id,
        dvaas::ExtractIdFromTaggedPacketInHex(
            test_outcome.test_run().test_vector().input().packet().hex()));
    filename = absl::StrCat(test_id, "_bmv2_textual_log.txt");
    dvaas::PacketTrace packet_trace = full_packet_trace_it->packet_trace();
    RETURN_IF_ERROR(dvaas_test_artifact_writer.AppendToTestArtifact(
        filename, packet_trace.bmv2_textual_log()));
  }
  return absl::OkStatus();
}

}  // namespace dvaas

#include "dvaas/packet_trace.h"

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
}  // namespace dvaas

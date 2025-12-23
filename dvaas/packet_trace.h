#ifndef PINS_DVAAS_PACKET_TRACE_H_
#define PINS_DVAAS_PACKET_TRACE_H_

#include "dvaas/packet_trace.pb.h"

namespace dvaas {

// Returns a copy of the packet trace with all the redundant information (bmv2
// textual log, hit/miss textual log) removed. This is done to reduce the
// size of the packet trace for better readability and also to make it more
// viable to store such traces for all test vectors.
dvaas::PacketTrace MakeCompactPacketTrace(dvaas::PacketTrace packet_trace);

}  // namespace dvaas

#endif  // PINS_DVAAS_PACKET_TRACE_H_

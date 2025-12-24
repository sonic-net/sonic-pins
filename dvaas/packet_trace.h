#ifndef PINS_DVAAS_PACKET_TRACE_H_
#define PINS_DVAAS_PACKET_TRACE_H_

#include <string>

#include "absl/status/status.h"
#include "dvaas/packet_trace.pb.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/gutil/test_artifact_writer.h"

namespace dvaas {

// Returns a copy of the packet trace with all the redundant information (bmv2
// textual log, hit/miss textual log) removed. This is done to reduce the
// size of the packet trace for better readability and also to make it more
// viable to store such traces for all test vectors.
dvaas::PacketTrace MakeCompactPacketTrace(dvaas::PacketTrace packet_trace);

// Returns a string of the packet trace summary for the given packet trace.
std::string GetPacketTraceSummary(const dvaas::PacketTrace& packet_trace);

// Stores the full BMv2 textual log for one of the acceptable outputs as a test
// artifact. Returns an error if none of the acceptable outputs have a full
// trace.
absl::Status StorePacketTraceTextualBmv2LogAsTestArtifact(
    PacketTestOutcome& test_outcome,
    gutil::TestArtifactWriter& dvaas_test_artifact_writer);

}  // namespace dvaas

#endif  // PINS_DVAAS_PACKET_TRACE_H_

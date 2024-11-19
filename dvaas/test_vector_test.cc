#include "dvaas/test_vector.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace dvaas {
namespace {

using ::gutil::IsOkAndHolds;
using ::testing::Eq;

TEST(MakeTestPacketTag, RoundTripsWithExtractTestPacketTag) {
  for (int test_packet_id : {0, 1, 2, 42, 1234}) {
    packetlib::Packet packet;
    packet.set_payload(MakeTestPacketTagFromUniqueId(test_packet_id));
    EXPECT_THAT(ExtractTestPacketTag(packet), IsOkAndHolds(Eq(test_packet_id)));
  }
}

}  // namespace
}  // namespace dvaas

#ifndef PINS_LIB_LACP_IXIA_HELPER_H_
#define PINS_LIB_LACP_IXIA_HELPER_H_

#include <string_view>

namespace pins_test::ixia {

inline constexpr std::string_view kLacpHeaderName = "LACP";

// LACP should be the second header in the stack after Ethernet.
inline constexpr int kLacpStackIndex = 2;

inline constexpr std::string_view kLacpDestinationMac = "01:80:c2:00:00:02";

// LACP field indices from the Ixia REST API:
namespace LacpField {

inline constexpr int kSubType = 1;
inline constexpr int kVersion = 2;
inline constexpr int kActorTlvType = 3;
inline constexpr int kActorTlvLength = 4;
inline constexpr int kActorSystemPriority = 5;
inline constexpr int kActorSystemId = 6;
inline constexpr int kActorKey = 7;
inline constexpr int kActorPortPriority = 8;
inline constexpr int kActorPortId = 9;
inline constexpr int kActorState = 10;
// Field 11 is reserved.
inline constexpr int kPartnerTlvType = 12;
inline constexpr int kPartnerTlvLength = 13;
inline constexpr int kPartnerSystemPriority = 14;
inline constexpr int kPartnerSystemId = 15;
inline constexpr int kPartnerKey = 16;
inline constexpr int kPartnerPortPriority = 17;
inline constexpr int kPartnerPortId = 18;
inline constexpr int kPartnerState = 19;
// Field 20 is reserved.
inline constexpr int kCollectorTlvType = 21;
inline constexpr int kCollectorTlvLength = 22;
inline constexpr int kCollectorMaxDelay = 23;
// Field 24 is reserved.
inline constexpr int kTerminatorTlvType = 25;
inline constexpr int kTerminatorTlvLength = 26;
// Field 27 is reserved.
inline constexpr int kFCS = 28;

}  // namespace LacpField

namespace LacpState {

inline constexpr int kActivity = 1 << 0;
inline constexpr int kTimeout = 1 << 1;
inline constexpr int kAggregation = 1 << 2;
inline constexpr int kSync = 1 << 3;
inline constexpr int kCollecting = 1 << 4;
inline constexpr int kDistributing = 1 << 5;
inline constexpr int kDefaulted = 1 << 6;
inline constexpr int kExpired = 1 << 7;

}  // namespace LacpState

}  // namespace pins_test::ixia

#endif  // PINS_LIB_LACP_IXIA_HELPER_H_

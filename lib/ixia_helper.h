// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_THINKIT_IXIA_INTERFACE_H_
#define PINS_THINKIT_IXIA_INTERFACE_H_

#include <array>
#include <cstdint>
#include <optional>
#include <string>
#include <variant>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "lib/ixia_helper.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/generic_testbed.h"

namespace pins_test::ixia {

inline constexpr int kEthernetStackIndex = 1;

inline constexpr std::string_view kEthernetWithoutFcsName =
    "Ethernet II without FCS";

inline constexpr std::string_view kFlowStatisticsView = "Flow Statistics";
inline constexpr std::string_view kTrafficItemStatisticsView =
    "Traffic Item Statistics";

// An Ixia port is defined by IP address of chassis, card number and
// port number.
// This structure holds these attributes which define an Ixia port.
struct IxiaPortInfo {
  std::string hostname;
  std::string card;
  std::string port;
};

// Structure represents a link between SUT and Ixia.
// This is represented by Ixia interface name and the SUT's gNMI interface
// name.
struct IxiaLink {
  std::string ixia_interface;
  std::string sut_interface;
  // Speed of the SUT interface in bits/second.
  int64_t sut_interface_bits_per_second = 0;
};

// Finds the ID of the JSON object in the array based on matching a given
// `field` to a desired `value`.
absl::StatusOr<int> FindIdByField(const thinkit::HttpResponse &response,
                                  absl::string_view field,
                                  absl::string_view desired_value);

// ExtractHref - Extract the href path from the Ixia response provided as
// input.  Returns either the href string or an error.
absl::StatusOr<std::string> ExtractHref(const thinkit::HttpResponse &resp);

// Extract ip, card and port from a fully qualified ixia interface name
// Ixia interface will look something like: "108.177.95.172/4/3" which is the
// IP address of chassis appended with the card number and port.
absl::StatusOr<IxiaPortInfo> ExtractPortInfo(absl::string_view ixia_interface);

// Sends the operation to the Ixia as a POST request
// and waits for it to finish if the operation returns IN_PROGRESS.
absl::Status SendAndWaitForComplete(absl::string_view operation_url,
                                    absl::string_view payload,
                                    thinkit::GenericTestbed &generic_testbed,
                                    absl::Duration timeout = absl::Seconds(60));

// IxiaConnect - connect to the Ixia.  returns the href from the response
// or an error.  takes the IP address of the Ixia as a string parameter,
// e.g. "A.B.C.D"
absl::StatusOr<std::string>
IxiaConnect(absl::string_view ixia_ip,
            thinkit::GenericTestbed &generic_testbed);

// IxiaVport - Connect to an Ixia Card/Port.  Returns either an error or the
// href string from the response. The card and port are supplied as e.g.
// "4" and "2". Takes in the href returned by IxiaConnect as a parameter. The
// return value is referred to as a vref in this namespace.
absl::StatusOr<std::string> IxiaVport(absl::string_view href,
                                      absl::string_view ixia_card,
                                      absl::string_view ixia_port,
                                      thinkit::GenericTestbed &generic_testbed);
absl::StatusOr<std::string>
IxiaVport(absl::string_view href,
          absl::string_view fully_qualified_ixia_interface_name,
          thinkit::GenericTestbed &generic_testbed);

// IxiaSession - starts an Ixia session.  Returns either an error or the
// href string for the first traffic item, e.g. something like
// "/api/v1/sessions/101/ixnetwork/traffic/trafficItem/1", which we'll refer
// to as a tref is this namespace. Takes in the vref returned by IxiaConnect
// as a parameter.
absl::StatusOr<std::string>
IxiaSession(absl::string_view vref, thinkit::GenericTestbed &generic_testbed);

// Sets up a traffic item with multiple sources and destinations, and optionally
// with a `traffic_name` useful for querying stats. Returns either an error or
// the href string for the first traffic item, e.g. something like
// "/api/v1/sessions/101/ixnetwork/traffic/trafficItem/1", which we'll refer
// to as a tref is this namespace. Takes in the vref returned by Ixia ports
// as parameters. `is_raw_pkt` indicates whether it is a raw traffic item.
absl::StatusOr<std::string> SetUpTrafficItemWithMultipleSrcsAndDsts(
    absl::Span<const std::string> sources,
    absl::Span<const std::string> destinations, std::string_view traffic_name,
    thinkit::GenericTestbed &testbed, bool is_raw_pkt = false);

// Sets up a traffic item with a single source and destination. Generates a
// unique name based on the source and destination.
absl::StatusOr<std::string> SetUpTrafficItem(
    absl::string_view vref_src, absl::string_view vref_dst,
    thinkit::GenericTestbed &generic_testbed);

// Sets up a traffic item with a single source and destination and a traffic
// name.
inline absl::StatusOr<std::string> SetUpTrafficItem(
    absl::string_view vref_src, absl::string_view vref_dst,
    absl::string_view traffic_name, thinkit::GenericTestbed &generic_testbed,
    bool is_raw_pkt = false) {
  return SetUpTrafficItemWithMultipleSrcsAndDsts(
      /*sources=*/{std::string(vref_src)},
      /*destinations=*/{std::string(vref_dst)}, traffic_name, generic_testbed,
      is_raw_pkt);
}

// Deletes traffic item. Takes in the tref returned by IxiaSession.
// Deleting a traffic item manually is not strictly required, but is useful
// when setting up a lot of items in a loop to not overwhelm the Ixia.
absl::Status DeleteTrafficItem(absl::string_view tref,
                               thinkit::GenericTestbed &testbed);

// Generates and applies traffic items. This prepares the traffic items for
// starting.
absl::Status GenerateAndApplyTrafficItems(
    absl::Span<const std::string> traffic_items,
    thinkit::GenericTestbed &testbed);

// Starts the traffic item, assuming it has already been generated and applied.
// This is useful to start items quicker when they are already prepared.
absl::Status StartTrafficItem(absl::string_view traffic_item,
                              thinkit::GenericTestbed &testbed);

// StartTraffic - starts traffic running from the Ixia, as previously
// configured before calling this function. user supplies the tref or
// traffic reference returned by IxiaSession and the href returned by
// IxiaConnect as parameters.
absl::Status StartTraffic(absl::string_view tref, absl::string_view href,
                          thinkit::GenericTestbed &generic_testbed);

// Same as above, except that `trefs` accept multiple traffics. By default,
// the traffics in `trefs` start in parallel; set `run_in_parallel` to false
// to start traffics sequentially.
absl::Status StartTraffic(absl::Span<const std::string> trefs,
                          absl::string_view href,
                          thinkit::GenericTestbed &generic_testbed,
                          bool run_in_parallel = true);

// StopTraffic - stops traffic running from the Ixia. StartTraffic is
// presumed to have been run first. Takes in the tref returned by IxiaSession
// as a parameter.
absl::Status StopTraffic(absl::string_view tref,
                         thinkit::GenericTestbed &generic_testbed);

// Same as above, except that `trefs` accept multiple traffics.
absl::Status StopTraffic(absl::Span<const std::string> trefs,
                         thinkit::GenericTestbed &generic_testbed);

// SetFrameRate - sets the frame rate for the traffic to be generated
// Takes in the tref returned by IxiaSession
absl::Status SetFrameRate(absl::string_view tref, float fps,
                          thinkit::GenericTestbed &generic_testbed);

// SetLineRate - sets the line rate as 1-100 percent of max line rate
// This is an alternative to SetFrameRate. Takes in the tref returned
// by IxiaSession
absl::Status SetLineRate(absl::string_view tref, int32_t percent,
                         thinkit::GenericTestbed &generic_testbed);

// SetFrameCount - sets the number of frames to send before stopping
// If this isn't called transmission will continue until manually stopped
// Takes in the tref returned by IxiaSession
absl::Status SetFrameCount(absl::string_view tref, int64_t frames,
                           thinkit::GenericTestbed &generic_testbed);

// SetFrameSize - sets the frame size
// If not called the frame size will default to 64 bytes
// Takes in the tref returned by IxiaSession
absl::Status SetFrameSize(absl::string_view tref, int32_t framesize,
                          thinkit::GenericTestbed &generic_testbed);

// Sets a field value for a stack of headers given the traffic item, header
// index, and the field index to a single fixed value.
absl::Status SetFieldSingleValue(absl::string_view tref, int stack_index,
                                 int field_index, absl::string_view value,
                                 thinkit::GenericTestbed &generic_testbed);

// Sets a field value for a stack of headers given the traffic item, header
// index, and the field index to a list of values that cycle.
absl::Status SetFieldValueList(absl::string_view tref, int stack_index,
                               int field_index,
                               absl::Span<const std::string> value,
                               thinkit::GenericTestbed &generic_testbed);

// Sets a field value to a random range with no duplicates.
// `min_value` and `max_value` are the min and max values of the range.
// `step` is the step size between each value.
// `seed` is the seed for the random number generator.
// `count` is the number of values to generate.
absl::Status SetFieldRandomRange(std::string_view tref, int stack_index,
                                 int field_index, std::string_view min_value,
                                 std::string_view max_value,
                                 std::string_view step, int seed, int count,
                                 thinkit::GenericTestbed &generic_testbed);

// SetDestMac - sets the destination MAC address for frames to be sent
// Takes in the tref returned by IxiaSession. dmac should be a string
// in the 'standard' hex format "xx:xx:xx:xx:xx:xx".
absl::Status SetDestMac(absl::string_view tref, absl::string_view dmac,
                        thinkit::GenericTestbed &generic_testbed);

// SetSrcMac - sets the source MAC address for frames to be sent
// Takes in the tref returned by IxiaSession
absl::Status SetSrcMac(absl::string_view tref, absl::string_view smac,
                       thinkit::GenericTestbed &generic_testbed);
// AppendIPv4 - set up to use an IPv4 header after the MAC.
// Takes in the tref returned by IxiaSession. If you don't call this
// or AppendIPv6 then an L2 packet will be sent.
absl::Status AppendIPv4(absl::string_view tref,
                        thinkit::GenericTestbed &generic_testbed);
// SetSrcIPv4 - set the source IPv4 address to use.
// Takes in the tref returned by IxiaSession
absl::Status SetSrcIPv4(absl::string_view tref, absl::string_view sip,
                        thinkit::GenericTestbed &generic_testbed);

// SetDestIPv4 - set the destination IPv4 address to use.
// Takes in the tref returned by IxiaSession
absl::Status SetDestIPv4(absl::string_view tref, absl::string_view dip,
                         thinkit::GenericTestbed &generic_testbed);

// AppendIPv6 - set up to use an IPv6 header after the MAC.
// Takes in the tref returned by IxiaSession. If you don't call this
// or AppendIPv4 then an L2 packet will be sent.
absl::Status AppendIPv6(absl::string_view tref,
                        thinkit::GenericTestbed &generic_testbed);

// SetSrcIPv6 - set the source IPv6 address to use.
// Takes in the tref returned by IxiaSession
absl::Status SetSrcIPv6(absl::string_view tref, absl::string_view sip,
                        thinkit::GenericTestbed &generic_testbed);

// SetDestIPv6 - set the destination IPv6 address to use.
// Takes in the tref returned by IxiaSession
absl::Status SetDestIPv6(absl::string_view tref, absl::string_view dip,
                         thinkit::GenericTestbed &generic_testbed);

// SetIpPriority - Set up to priority field in IP header using dscp value
// and ECN bits.
// Takes in the tref returned by SetUpTrafficItem.
absl::Status SetIpPriority(absl::string_view tref, int dscp, int ecn_bits,
                           bool is_ipv4,
                           thinkit::GenericTestbed &generic_testbed);

// SetIpTTL - Sets the TTL field in IP header.
// Takes in the tref returned by SetUpTrafficItem.
absl::Status SetIpTTL(absl::string_view tref, int ttl, bool is_ipv4,
                      thinkit::GenericTestbed &generic_testbed);

// Removes the protocol at the given index.
absl::Status RemoveProtocolAtIndex(absl::string_view tref, int index,
                                   thinkit::GenericTestbed &generic_testbed);

// AppendTcp - Append TCP template to IP header.
// Takes in the tref returned by SetUpTrafficItem.
absl::Status AppendTcp(absl::string_view tref,
                       thinkit::GenericTestbed &generic_testbed);

// AppendUdp - Append UDP template to IP header.
// Takes in the tref returned by SetUpTrafficItem.
absl::Status AppendUdp(absl::string_view tref,
                       thinkit::GenericTestbed &generic_testbed);

// AppendProtocolAtStack - Appends the provided protocol template to the
// existing stack of headers as specified. Takes in the tref returned by
// SetUpTrafficItem. NOTE: The protocol needs to be the exact string in the
// `displayName` for the specific template to be added. Some examples: ARP ->
// "Ethernet ARP", IPv4 -> "IPv4"
absl::Status AppendProtocolAtStack(absl::string_view tref,
                                   absl::string_view protocol,
                                   absl::string_view stack,
                                   thinkit::GenericTestbed &generic_testbed);

absl::Status AppendPfc(absl::string_view tref, absl::string_view stack,
                       thinkit::GenericTestbed &generic_testbed);
// -- High-level API for setting traffic item parameters -----------------------

// The priority fields of an IP packet. Aka "type of service" for IPv4 and
// "traffic class" for IPv6.
struct IpPriority {
  int dscp = 0; // 6 bits.
  int ecn = 0;  // 2 bits.
};

struct Ipv4TrafficParameters {
  netaddr::Ipv4Address src_ipv4 = netaddr::Ipv4Address(192, 168, 0, 1);
  netaddr::Ipv4Address dst_ipv4 = netaddr::Ipv4Address(172, 0, 0, 1);
  std::optional<IpPriority> priority;
};

struct Ipv6TrafficParameters {
  netaddr::Ipv6Address src_ipv6 =
      netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, 1); // 1000::1;
  netaddr::Ipv6Address dst_ipv6 =
      netaddr::Ipv6Address(0x2000, 0, 0, 0, 0, 0, 0, 2); // 2000::2;
  std::optional<IpPriority> priority;
};

struct PfcTrafficParameters {
  uint8_t priority_enable_vector = 0;
  std::array<uint16_t, 8> pause_quanta_per_queue = {0, 0, 0, 0, 0, 0, 0, 0};
};

// The number of frames to send per second.
struct FramesPerSecond {
  int frames_per_second = 0;
};
// Alternative to `FramesPerSecond`. Sets speed as percent of max line rate.
struct PercentOfMaxLineRate {
  int percent_of_max_line_rate = 0;
};

// Various configurable parameters of an Ixia traffic item.
struct TrafficParameters {
  // The number of frames to send before stopping. If unset, traffic will
  // continue until manually stopped.
  std::optional<int64_t> frame_count;
  // The frame size. If unset, will default to 64 bytes.
  std::optional<int32_t> frame_size_in_bytes;
  // The speed at which to send frames (required).
  std::variant<FramesPerSecond, PercentOfMaxLineRate> traffic_speed;

  // The source MAC to use in the test frames.
  netaddr::MacAddress src_mac = netaddr::MacAddress(2, 2, 2, 2, 2, 2);
  // The destination MAC to use in the test frames.
  netaddr::MacAddress dst_mac = netaddr::MacAddress(0, 1, 2, 3, 4, 5);

  // The IP fields to use in the test frames. If unset, L2 frame without L3
  // header will be sent.
  std::optional<std::variant<Ipv4TrafficParameters, Ipv6TrafficParameters>>
      ip_parameters;
  std::optional<PfcTrafficParameters> pfc_parameters;
};

// Sets any given parameters for the given traffic item.
// Takes in the tref returned by IxiaSession / SetUpTrafficItem.
absl::Status SetTrafficParameters(absl::string_view tref,
                                  const TrafficParameters &params,
                                  thinkit::GenericTestbed &testbed,
                                  bool is_update = false);

// Sets the priority enable vector field in the PFC header.
absl::Status SetPfcPriorityEnableVector(
    absl::string_view tref, uint8_t priority_enable_vector,
    thinkit::GenericTestbed &generic_testbed);

// Sets the pause quanta values for queues in the PFC header.
absl::Status SetPfcQueuePauseQuanta(
    absl::string_view tref, const std::array<uint16_t, 8> &queue_pause_quanta,
    thinkit::GenericTestbed &generic_testbed);

// -- Statistics ---------------------------------------------------------------

// Low-level function for obtaining unparsed statistics view by index.
// Queries `statistics/view/<index>`.
// Takes in the href returned by IxiaConnect.
absl::StatusOr<std::string>
GetRawStatsView(absl::string_view href, int stats_view_index,
                thinkit::GenericTestbed &generic_testbed);

// Returns statistics for the traffic item of the given name.
// Takes in the href returned by IxiaConnect, and the `traffic_item_name` set
// by `SetUpTrafficItem`.
absl::StatusOr<TrafficItemStats>
GetTrafficItemStats(absl::string_view href, absl::string_view traffic_item_name,
                    thinkit::GenericTestbed &generic_testbed);

// Returns statistics for all traffic items, keyed by traffic item name.
// Takes in the href returned by IxiaConnect, and the `traffic_item_name` set
// by `SetUpTrafficItem`. `view_name` is the name of the statistics view in the
// GUI (e.g. Traffic Item Statistics).
absl::StatusOr<TrafficStats> GetAllTrafficItemStats(
    absl::string_view href, thinkit::GenericTestbed &generic_testbed,
    absl::string_view view_name = kFlowStatisticsView);

// Computes average rate (bytes/s) at which traffic was received back by Ixia.
inline double BytesPerSecondReceived(const TrafficItemStats &stats) {
  // If the first timestamp is 0, this means no traffic has been received.
  if (stats.first_time_stamp() == 0.0) {
    return 0.0;
  }
  return stats.rx_bytes() /
         (stats.last_time_stamp() - stats.first_time_stamp());
}

// Takes unparsed traffic item statistics, as returned by `GetRawStatsView`, and
// returns parsed representation, keyed by traffic item name.
// Return Unavailable error if the stats are not ready yet.
absl::StatusOr<TrafficStats> ParseTrafficItemStats(absl::string_view raw_stats);

// Go over the connections and return vector of connections
// whose links are up.
absl::StatusOr<std::vector<IxiaLink>>
GetReadyIxiaLinks(thinkit::GenericTestbed &generic_testbed,
                  gnmi::gNMI::StubInterface &gnmi_stub);

// Returns Ixia link information for requested `port` on switch connected to
// Ixia. Returns failure status if Ixia link information is not found.
absl::StatusOr<IxiaLink> GetIxiaLink(thinkit::GenericTestbed &generic_testbed,
                                     gnmi::gNMI::StubInterface &gnmi_stub,
                                     const std::string &switch_port);

// Connects to Ixia on the given testbed and returns a string handle identifying
// the connection (aka "topology ref").
absl::StatusOr<std::string> ConnectToIxia(thinkit::GenericTestbed &testbed);

// Converts an integer to a hex string. Does not add a leading "0x".
inline std::string ToHex(int value) { return absl::StrCat(absl::Hex(value)); }

} // namespace pins_test::ixia

#endif // PINS_THINKIT_IXIA_INTERFACE_H_

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

#include <cstdint>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "lib/ixia_helper.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "thinkit/generic_testbed.h"

namespace pins_test::ixia {

// An Ixia port is defined by IP address of chassis, card number and
// port number.
// This structure holds these attributes which define an Ixia port.
struct IxiaPortInfo {
  std::string hostname;
  std::string card;
  std::string port;
};

// ExtractHref - Extract the href path from the Ixia response provided as
// input.  Returns either the href string or an error.
absl::StatusOr<std::string> ExtractHref(thinkit::HttpResponse &resp);

// Extract ip, card and port from a fully qualified ixia interface name
// Ixia interface will look something like: "108.177.95.172/4/3" which is the
// IP address of chassis appended with the card number and port.
absl::StatusOr<IxiaPortInfo> ExtractPortInfo(absl::string_view ixia_interface);

// WaitForComplete - Checks the http response provided and if 202 was returned,
// then check for IN_PROGRESS and if so polls until complete.  it returns
// the href url from the response or an error. the timeout can be provided
// if desired, and defaults to 1 minute if not. the timeout determines how
// long we'll wait for the IN_PROGRESS to resolve. if the elapsed time exceeds
// the timeout provided we'll return an error.
absl::Status WaitForComplete(const thinkit::HttpResponse &response,
                             thinkit::GenericTestbed &generic_testbed,
                             absl::Duration timeout = absl::Seconds(60));

// IxiaConnect - connect to the Ixia.  returns the href from the response
// or an error.  takes the IP address of the Ixia as a string parameter,
// e.g. "A.B.C.D"
absl::StatusOr<std::string> IxiaConnect(
    absl::string_view ixia_ip, thinkit::GenericTestbed &generic_testbed);

// IxiaVport - Connect to an Ixia Card/Port.  Returns either an error or the
// href string from the response. The card and port are supplied as e.g.
// "4" and "2". Takes in the href returned by IxiaConnect as a parameter. The
// return value is referred to as a vref in this namespace.
absl::StatusOr<std::string> IxiaVport(absl::string_view href,
                                      absl::string_view ixia_card,
                                      absl::string_view ixia_port,
                                      thinkit::GenericTestbed &generic_testbed);
absl::StatusOr<std::string> IxiaVport(
    absl::string_view href,
    absl::string_view fully_qualified_ixia_interface_name,
    thinkit::GenericTestbed &generic_testbed);

// IxiaSession - starts an Ixia session.  Returns either an error or the
// href string for the first traffic item, e.g. something like
// "/api/v1/sessions/101/ixnetwork/traffic/trafficItem/1", which we'll refer
// to as a tref is this namespace. Takes in the vref returned by IxiaConnect
// as a parameter.
absl::StatusOr<std::string> IxiaSession(
    absl::string_view vref, thinkit::GenericTestbed &generic_testbed);

// SetUpTrafficItem - Sets up a traffic item with source and destination,
// and optionally with a `traffic_name` useful for querying stats.
// Returns either an error or the
// href string for the first traffic item, e.g. something like
// "/api/v1/sessions/101/ixnetwork/traffic/trafficItem/1", which we'll refer
// to as a tref is this namespace. Takes in the vref returned by Ixia ports
// as parameters.
absl::StatusOr<std::string> SetUpTrafficItem(
    absl::string_view vref_src, absl::string_view vref_dst,
    thinkit::GenericTestbed &generic_testbed);
absl::StatusOr<std::string> SetUpTrafficItem(
    absl::string_view vref_src, absl::string_view vref_dst,
    absl::string_view traffic_name, thinkit::GenericTestbed &generic_testbed);

// Deletes traffic item. Takes in the tref returned by IxiaSession.
// Deleting a traffic item manually is not strictly required, but is useful
// when setting up a lot of items in a loop to not overwhelm the Ixia.
absl::Status DeleteTrafficItem(absl::string_view tref,
                               thinkit::GenericTestbed &testbed);

// StartTraffic - starts traffic running from the Ixia, as previously
// configured before calling this function. user supplies the tref or
// traffic reference returned by IxiaSession and the href returned by
// IxiaConnect as parameters.
absl::Status StartTraffic(absl::string_view tref, absl::string_view href,
                          thinkit::GenericTestbed &generic_testbed);

// Same as above, except that `trefs` accept multiple traffics.
absl::Status StartTraffic(absl::Span<const std::string> trefs,
                          absl::string_view href,
                          thinkit::GenericTestbed &generic_testbed);

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
absl::Status SetFrameRate(absl::string_view tref, uint32_t fps,
                          thinkit::GenericTestbed &generic_testbed);

// SetLineRate - sets the line rate as 1-100 percent of max line rate
// This is an alternative to SetFrameRate. Takes in the tref returned
// by IxiaSession
absl::Status SetLineRate(absl::string_view tref, uint32_t percent,
                         thinkit::GenericTestbed &generic_testbed);

// SetFrameCount - sets the number of frames to send before stopping
// If this isn't called transmission will continue until manually stopped
// Takes in the tref returned by IxiaSession
absl::Status SetFrameCount(absl::string_view tref, uint32_t frames,
                           thinkit::GenericTestbed &generic_testbed);

// SetFrameSize - sets the frame size
// If not called the frame size will default to 64 bytes
// Takes in the tref returned by IxiaSession
absl::Status SetFrameSize(absl::string_view tref, uint32_t framesize,
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

// -- High-level API for setting traffic item parameters -----------------------

// The priority fields of an IP packet. Aka "type of service" for IPv4 and
// "traffic class" for IPv6.
struct IpPriority {
  int dscp = 0;  // 6 bits.
  int ecn = 0;   // 2 bits.
};

struct Ipv4TrafficParameters {
  netaddr::Ipv4Address src_ipv4 = netaddr::Ipv4Address(192, 168, 0, 1);
  netaddr::Ipv4Address dst_ipv4 = netaddr::Ipv4Address(172, 0, 0, 1);
  std::optional<IpPriority> priority;
};

struct Ipv6TrafficParameters {
  netaddr::Ipv6Address src_ipv6 =
      netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, 1);  // 1000::1;
  netaddr::Ipv6Address dst_ipv6 =
      netaddr::Ipv6Address(0x2000, 0, 0, 0, 0, 0, 0, 2);  // 2000::2;
  std::optional<IpPriority> priority;
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
  std::optional<int> frame_count;
  // The frame size. If unset, will default to 64 bytes.
  std::optional<int> frame_size_in_bytes;
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
};

// Sets any given parameters for the given traffic item.
// Takes in the tref returned by IxiaSession / SetUpTrafficItem.
absl::Status SetTrafficParameters(absl::string_view tref,
                                  const TrafficParameters &params,
                                  thinkit::GenericTestbed &testbed);

// -- Statistics ---------------------------------------------------------------

// Low-level function for obtaining unparsed statistics view by index.
// Queries `statistics/view/<index>`.
// Takes in the href returned by IxiaConnect.
absl::StatusOr<std::string> GetRawStatsView(
    absl::string_view href, int stats_view_index,
    thinkit::GenericTestbed &generic_testbed);

// Returns statistics for the traffic item of the given name.
// Takes in the href returned by IxiaConnect, and the `traffic_item_name` set
// by `SetUpTrafficItem`.
absl::StatusOr<TrafficItemStats> GetTrafficItemStats(
    absl::string_view href, absl::string_view traffic_item_name,
    thinkit::GenericTestbed &generic_testbed);

// Returns statistics for all traffic items, keyed by traffic item name.
// Takes in the href returned by IxiaConnect, and the `traffic_item_name` set
// by `SetUpTrafficItem`.
absl::StatusOr<TrafficStats> GetAllTrafficItemStats(
    absl::string_view href, thinkit::GenericTestbed &generic_testbed);

// Computes average rate (bytes/s) at which traffic was received back by Ixia.
inline double BytesPerSecondReceived(const TrafficItemStats &stats) {
  return stats.rx_bytes() /
         (stats.last_time_stamp() - stats.first_time_stamp());
}

// Takes unparsed traffic item statistics, as returned by `GetRawStatsView`, and
// returns parsed representation, keyed by traffic item name.
// Return Unavailable error if the stats are not ready yet.
absl::StatusOr<TrafficStats> ParseTrafficItemStats(absl::string_view raw_stats);

}  // namespace pins_test::ixia

#endif  // PINS_THINKIT_IXIA_INTERFACE_H_

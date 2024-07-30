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

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
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
// "4" and "2". Takes in the href returned by IxiaConnect as a parameter.  The
// return value is referred to as a vref in this namespace.
absl::StatusOr<std::string> IxiaVport(absl::string_view href,
                                      absl::string_view ixia_card,
                                      absl::string_view ixia_port,
                                      thinkit::GenericTestbed &generic_testbed);

// IxiaSession - starts an Ixia session.  Returns either an error or the
// href string for the first traffic item, e.g. something like
// "/api/v1/sessions/101/ixnetwork/traffic/trafficItem/1", which we'll refer
// to as a tref is this namespace. Takes in the vref returned by IxiaConnect
// as a parameter.
absl::StatusOr<std::string> IxiaSession(
    absl::string_view vref, thinkit::GenericTestbed &generic_testbed);

// SetUpTrafficItem - Sets up a traffic item with source and destination.
// Returns either an error or the
// href string for the first traffic item, e.g. something like
// "/api/v1/sessions/101/ixnetwork/traffic/trafficItem/1", which we'll refer
// to as a tref is this namespace. Takes in the vref returned by Ixia ports
// as parameters.
absl::StatusOr<std::string> SetUpTrafficItem(
    absl::string_view vref_src, absl::string_view vref_dst,
    thinkit::GenericTestbed &generic_testbed);

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
// presumed to have been run first.  Takes in the tref returned by IxiaSession
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
// This is an alternative to SetFrameRate.  Takes in the tref returned
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
// AppendIPv4 - set up to use an IPv4 header after the MAC
// Takes in the tref returned by IxiaSession.  if you don't call this
// or AppendIPv6 then an L2 packet will be sent.
absl::Status AppendIPv4(absl::string_view tref,
                        thinkit::GenericTestbed &generic_testbed);
// SetSrcIPv4 - set the source IPv4 address to use
// Takes in the tref returned by IxiaSession
absl::Status SetSrcIPv4(absl::string_view tref, absl::string_view sip,
                        thinkit::GenericTestbed &generic_testbed);

// SetDestIPv4 - set the destination IPv4 address to use
// Takes in the tref returned by IxiaSession
absl::Status SetDestIPv4(absl::string_view tref, absl::string_view dip,
                         thinkit::GenericTestbed &generic_testbed);

// AppendIPv6 - set up to use an IPv6 header after the MAC
// Takes in the tref returned by IxiaSession.  if you don't call this
// or AppendIPv4 then an L2 packet will be sent.
absl::Status AppendIPv6(absl::string_view tref,
                        thinkit::GenericTestbed &generic_testbed);

// SetSrcIPv6 - set the source IPv4 address to use
// Takes in the tref returned by IxiaSession
absl::Status SetSrcIPv6(absl::string_view tref, absl::string_view sip,
                        thinkit::GenericTestbed &generic_testbed);

// SetDestIPv6 - set the source IPv4 address to use
// Takes in the tref returned by IxiaSession
absl::Status SetDestIPv6(absl::string_view tref, absl::string_view dip,
                         thinkit::GenericTestbed &generic_testbed);

// SetPriority - Set up to priority field in IP header using dscp value
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

}  // namespace pins_test::ixia

#endif  // PINS_THINKIT_IXIA_INTERFACE_H_

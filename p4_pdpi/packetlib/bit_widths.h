// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#ifndef PINS_P4_PDPI_PACKETLIB_BIT_WIDTHS_H_
#define PINS_P4_PDPI_PACKETLIB_BIT_WIDTHS_H_

// Bit widths of packet fields. Naming convention is:
//   "k" <header-name> <field-name> "Bitwidth"
// Some headers may be combined, e.g. Ip for IPv4 and IPv6.
namespace packetlib {

// Standard header sizes (for headers without extensions, etc).
constexpr int kEthernetHeaderBitwidth = 48 * 2 + 16;
constexpr int kStandardIpv4HeaderBitwidth = 160;
constexpr int kIpv6HeaderBitwidth = 320;
constexpr int kMinHopByHopOptionsHeaderBitwidth = 64;
constexpr int kUdpHeaderBitwidth = 64;
constexpr int kStandardTcpHeaderBitwidth = 5 * 32;
constexpr int kArpHeaderBitwidth = 28 * 8;
constexpr int kIcmpHeaderBitwidth = 8 * 8;
constexpr int kVlanHeaderBitwidth = 32;
constexpr int kRfc2784GreHeaderWithoutOptionalsBitwidth = 32;
constexpr int kSaiP4BMv2PacketInHeaderBitwidth = 24;
constexpr int kIpfixHeaderBitwidth = 128;
constexpr int kPsampHeaderBitwidth = 224;
constexpr int kPtpHeaderBitwidth = 272;
constexpr int kPspHeaderBitwidth = 128;
constexpr int kCsigHeaderBitwidth = 32;

// Ethernet constants.
constexpr int kEthernetEthertypeBitwidth = 16;

// VLAN constants.
constexpr int kVlanPriorityCodePointBitwidth = 3;
constexpr int kVlanDropEligibilityIndicatorBitwidth = 1;
constexpr int kVlanVlanIdentifierBitwidth = 12;
constexpr int kVlanEthertypeBitwidth = 16;

// CSIG constants.
constexpr int kCsigSignalTypeBitwidth = 3;
constexpr int kCsigReserved0Bitwidth = 1;
constexpr int kCsigSignalValueBitwidth = 5;
constexpr int kCsigLocatorMetadataBitwidth = 7;
constexpr int kCsigEthertypeBitwidth = 16;

// IP constants.
constexpr int kIpVersionBitwidth = 4;         // IPv4 & IPv6
constexpr int kIpIhlBitwidth = 4;             // IPv4
constexpr int kIpDscpBitwidth = 6;            // IPv4 & IPv6
constexpr int kIpEcnBitwidth = 2;             // IPv4 & IPv6
constexpr int kIpTotalLengthBitwidth = 16;    // IPv4
constexpr int kIpIdentificationBitwidth = 16; // IPv4
constexpr int kIpFlagsBitwidth = 3;           // IPv4
constexpr int kIpFragmentOffsetBitwidth = 13; // IPv4
constexpr int kIpTtlBitwidth = 8;             // IPv4
constexpr int kIpProtocolBitwidth = 8;        // IPv4
constexpr int kIpChecksumBitwidth = 16;       // IPv4
constexpr int kIpFlowLabelBitwidth = 20;      // IPv6
constexpr int kIpPayloadLengthBitwidth = 16;  // IPv6
constexpr int kIpNextHeaderBitwidth = 8;      // IPv6
constexpr int kIpHopLimitBitwidth = 8;        // IPv6

// IPv6 hop-by-hop options extension constants.
constexpr int kHopByHopNextHeaderBitwidth = 8;             // IPv6 Options
constexpr int kHopByHopHeaderExtensionLengthBitwidth = 8;  // IPv6 Options
constexpr int kHopByHopOptionsAndPaddingBitwidth = 48;     // IPv6 Options
// Note: The rest of the `HopByHopOptionsHeader` is represented by
// `more_options_and_padding`, which has a variable length bit-width based on
// the `header_extension_length`.

// UDP constants.
constexpr int kUdpPortBitwidth = 16;
constexpr int kUdpLengthBitwidth = 16;
constexpr int kUdpChecksumBitwidth = 16;

// TCP constants.
constexpr int kTcpPortBitwidth = 16;
constexpr int kTcpSequenceNumberBitwidth = 32;
constexpr int kTcpAcknowledgementNumberBitwidth = 32;
constexpr int kTcpDataOffsetBitwidth = 4;
constexpr int kTcpRestOfHeaderBitwidth = 60;

// ARP constants.
constexpr int kArpTypeBitwidth = 16;
constexpr int kArpLengthBitwidth = 8;
constexpr int kArpOperationBitwidth = 16;

// ICMP constants.
constexpr int kIcmpTypeBitwidth = 8;
constexpr int kIcmpCodeBitwidth = 8;
constexpr int kIcmpChecksumBitwidth = 16;
constexpr int kIcmpRestOfHeaderBitwidth = 32;

// GRE constants.
constexpr int kGreChecksumPresentBitwidth = 1;
constexpr int kGreReserved0Bitwidth = 12;
constexpr int kGreVersionBitwidth = 3;
constexpr int kGreProtocolTypeBitwidth = 16;
constexpr int kGreChecksumBitwidth = 16;
constexpr int kGreReserved1Bitwidth = 16;

// Minimum packet sizes, in bytes.
constexpr int kMinNumBytesInEthernetPayload = 46;

// SAI P4 packet_in header on BMv2 targets constants.
constexpr int kSaiP4BMv2PacketInIngressPortBitwidth = 9;
constexpr int kSaiP4BMv2PacketInTargetEgressPortBitwidth = 9;
constexpr int kSaiP4BMv2PacketInUnusedPadBitwidth = 6;

// IPFIX constants.
constexpr int kIpfixVersionBitwidth = 16;
constexpr int kIpfixLengthBitwidth = 16;
constexpr int kIpfixExportTimeBitwidth = 32;
constexpr int kIpfixSequenceNumberBitwidth = 32;
constexpr int kIpfixObservationDomainIdBitwidth = 32;

// PSAMP constants
constexpr int kPsampTemplateIdBitwidth = 16;
constexpr int kPsampLengthBitwidth = 16;
constexpr int kPsampObservationTimeBitwidth = 64;
constexpr int kPsampFlowsetBitwidth = 16;
constexpr int kPsampNextHopIndexBitwidth = 16;
constexpr int kPsampEpochBitwidth = 16;
constexpr int kPsampIngressPortBitwidth = 16;
constexpr int kPsampEgressPortBitwidth = 16;
constexpr int kPsampUserMetaFieldBitwidth = 16;
constexpr int kPsampDlbIdBitwidth = 8;
constexpr int kPsampVariableLengthBitwidth = 8;
constexpr int kPsampPacketSampledLengthBitwidth = 16;

// PTP constants
constexpr int kPtpTransportSpecificBitwidth = 4;
constexpr int kPtpMessageTypeBitwidth = 4;
constexpr int kPtpReserved0Bitwidth = 4;
constexpr int kPtpVersionPtpBitwidth = 4;
constexpr int kPtpMessageLengthBitwidth = 16;
constexpr int kPtpDomainNumberBitwidth = 8;
constexpr int kPtpReserved1Bitwidth = 8;
constexpr int kPtpFlagsBitwidth = 16;
constexpr int kPtpCorrectionFieldBitwidth = 64;
constexpr int kPtpReserved2Bitwidth = 32;
constexpr int kPtpSourcePortIdentityBitwidth = 80;
constexpr int kPtpSequenceIdBitwidth = 16;
constexpr int kPtpControlFieldBitwidth = 8;
constexpr int kPtpLogMessageIntervalBitwidth = 8;

// PSP constants
// NOTE: There is an optional virtualization_cookie field that we do not model
// since we do not yet have a use-case.
constexpr int kPspNextHeaderBitwidth = 8;
constexpr int kPspHeaderExtLengthBitwidth = 8;
constexpr int kPspReserved0Bitwidth = 2;
constexpr int kPspCryptOffsetBitwidth = 6;
constexpr int kPspSampleBitwidth = 1;
constexpr int kPspDropBitwidth = 1;
constexpr int kPspVersionBitwidth = 4;
constexpr int kPspVirtualizationCookieBitwidth = 1;
constexpr int kPspReserved1Bitwidth = 1;
constexpr int kPspSecurityParametersIndexBitwidth = 32;
constexpr int kPspInitializationVectorBitwidth = 64;

} // namespace packetlib

#endif // PINS_P4_PDPI_PACKETLIB_BIT_WIDTHS_H_

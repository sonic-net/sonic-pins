// Copyright 2020 Google LLC
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

#include "p4_pdpi/utils/ir.h"

#include <arpa/inet.h>
#include <ctype.h>
#include <endian.h>
#include <errno.h>
#include <net/ethernet.h>
#include <netinet/ether.h>
#include <netinet/in.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/types.h>

#include <algorithm>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/escaping.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "google/protobuf/map.h"
#include "google/rpc/code.pb.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"

namespace pdpi {

using ::netaddr::Ipv4Address;
using ::netaddr::Ipv6Address;
using ::netaddr::MacAddress;
using ::pdpi::Format;
using ::pdpi::IrValue;

absl::StatusOr<std::string> ArbitraryToNormalizedByteString(
    const std::string &bytes, int expected_bitwidth) {
  std::string canonical_string = ArbitraryToCanonicalByteString(bytes);
  const int bitwidth = GetBitwidthOfByteString(canonical_string);
  if (bitwidth > expected_bitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Bytestring of length " << bitwidth << " bits does not fit in "
           << expected_bitwidth << " bits.";
  }

  const int num_bytes = (expected_bitwidth + 7) / 8;
  return absl::StrCat(std::string(num_bytes - canonical_string.length(), 0),
                      canonical_string);
}

absl::StatusOr<uint64_t> ArbitraryByteStringToUint(const std::string &bytes,
                                                   int bitwidth) {
  if (bitwidth > 64) {
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        absl::StrCat("Cannot convert value with "
                                     "bitwidth ",
                                     bitwidth, " to uint."));
  }
  ASSIGN_OR_RETURN(const auto &stripped_value,
                   ArbitraryToNormalizedByteString(bytes, bitwidth));
  uint64_t nb_value;  // network byte order
  char value[sizeof(nb_value)];
  const int pad = static_cast<int>(sizeof(nb_value)) -
                  static_cast<int>(stripped_value.size());
  if (pad) {
    memset(value, 0, pad);
  }
  memcpy(value + pad, stripped_value.data(), stripped_value.size());
  memcpy(&nb_value, value, sizeof(nb_value));

  return be64toh(nb_value);
}

absl::StatusOr<std::string> UintToNormalizedByteString(uint64_t value,
                                                       int bitwidth) {
  if (bitwidth <= 0 || bitwidth > 64) {
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        absl::StrCat("Cannot convert value with "
                                     "bitwidth ",
                                     bitwidth, " to ByteString."));
  }
  std::string bytes = "";
  if (bitwidth <= 8) {
    uint8_t tmp = static_cast<uint8_t>(value);
    bytes.assign(reinterpret_cast<char *>(&tmp), sizeof(uint8_t));
  } else if (bitwidth <= 16) {
    uint16_t tmp = htons(static_cast<uint16_t>(value));
    bytes.assign(reinterpret_cast<char *>(&tmp), sizeof(uint16_t));
  } else if (bitwidth <= 32) {
    uint32_t tmp = htonl(static_cast<uint32_t>(value));
    bytes.assign(reinterpret_cast<char *>(&tmp), sizeof(uint32_t));
  } else {
    uint64_t tmp =
        (htonl(1) == 1)
            ? value
            : (static_cast<uint64_t>(htonl(value)) << 32) | htonl(value >> 32);
    bytes.assign(reinterpret_cast<char *>(&tmp), sizeof(uint64_t));
  }

  ASSIGN_OR_RETURN(auto normalized_str,
                   ArbitraryToNormalizedByteString(bytes, bitwidth));

  return normalized_str;
}

std::string ArbitraryToCanonicalByteString(std::string bytes) {
  // Remove leading zeros.
  bytes.erase(0, std::min(bytes.find_first_not_of('\x00'), bytes.size() - 1));
  return bytes;
}

int GetBitwidthOfByteString(const std::string &input_string) {
  if (input_string.empty()) return 0;

  // Use str.length() - 1. MSB will need to be handled separately since it
  // can have leading zeros which should not be counted.
  int length_in_bits = (input_string.length() - 1) * kNumBitsInByte;

  uint8_t msb;
  memcpy(&msb, &input_string[0], 1);
  while (msb != 0) {
    ++length_in_bits;
    msb >>= 1;
  }

  return length_in_bits;
}

absl::StatusOr<Format> GetFormat(const std::vector<std::string> &annotations,
                                 const int bitwidth, bool is_sdn_string) {
  Format format = Format::HEX_STRING;
  if (is_sdn_string) {
    format = Format::STRING;
  }
  for (const std::string &annotation : annotations) {
    if (absl::StartsWith(annotation, "@format(")) {
      if (format != Format::HEX_STRING) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Found conflicting formatting annotations.";
      }
      if (annotation == "@format(MAC_ADDRESS)") {
        format = Format::MAC;
      } else if (annotation == "@format(IPV4_ADDRESS)") {
        format = Format::IPV4;
      } else if (annotation == "@format(IPV6_ADDRESS)") {
        format = Format::IPV6;
      } else {
        return gutil::InvalidArgumentErrorBuilder()
               << "Found invalid format annotation: '" << annotation << "'.";
      }
    }
  }
  if (format == Format::MAC && bitwidth != kNumBitsInMac) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Only 48 bit values can be formatted as a MAC address.";
  }
  if (format == Format::IPV4 && bitwidth != kNumBitsInIpv4) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Only 32 bit values can be formatted as an IPv4 address.";
  }
  if (format == Format::IPV6 && bitwidth != kNumBitsInIpv6) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Only 128 bit values can be formatted as an IPv6 address.";
  }
  return format;
}

absl::StatusOr<IrValue> ArbitraryByteStringToIrValue(Format format,
                                                     const int bitwidth,
                                                     const std::string &bytes) {
  IrValue result;
  switch (format) {
    case Format::MAC: {
      ASSIGN_OR_RETURN(auto mac, MacAddress::OfByteString(bytes));
      result.set_mac(mac.ToString());
      return result;
    }
    case Format::IPV4: {
      ASSIGN_OR_RETURN(auto ipv4, Ipv4Address::OfByteString(bytes));
      result.set_ipv4(ipv4.ToString());
      return result;
    }
    case Format::IPV6: {
      ASSIGN_OR_RETURN(auto ipv6, Ipv6Address::OfByteString(bytes));
      result.set_ipv6(ipv6.ToString());
      return result;
    }
    case Format::STRING: {
      result.set_str(bytes);
      return result;
    }
    case Format::HEX_STRING: {
      ASSIGN_OR_RETURN(std::string normalized_bytes,
                       ArbitraryToNormalizedByteString(bytes, bitwidth));
      std::string hex_string = absl::BytesToHexString(normalized_bytes);
      const int expected_num_hex_chars =
          bitwidth / 4 + (bitwidth % 4 != 0 ? 1 : 0);
      if (expected_num_hex_chars != hex_string.size()) {
        // absl::BytesToHexString operates on bytes (= 8 bits), but we want to
        // operate on nibbles (= 4 bits). This fixes the length as necessary.
        hex_string = hex_string.substr(1);
      }
      result.set_hex_str(absl::StrCat("0x", hex_string));
      return result;
    }
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unexpected format: " << Format_Name(format);
  }
}

absl::Status ValidateIrValueFormat(const IrValue &ir_value, Format format) {
  const auto &format_case = ir_value.format_case();
  ASSIGN_OR_RETURN(const std::string format_case_name,
                   gutil::GetOneOfFieldName(ir_value, std::string("format")));
  switch (format) {
    case Format::MAC: {
      if (format_case != IrValue::kMac) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Expected format '" << Format_Name(Format::MAC)
               << "', but got '" << absl::AsciiStrToUpper(format_case_name)
               << "' instead.";
      }
      break;
    }
    case Format::IPV4: {
      if (format_case != IrValue::kIpv4) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Expected format '" << Format_Name(Format::IPV4)
               << "', but got '" << absl::AsciiStrToUpper(format_case_name)
               << "' instead.";
      }
      break;
    }
    case Format::IPV6: {
      if (format_case != IrValue::kIpv6) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Expected format '" << Format_Name(Format::IPV6)
               << "', but got '" << absl::AsciiStrToUpper(format_case_name)
               << "' instead.";
      }
      break;
    }
    case Format::STRING: {
      if (format_case != IrValue::kStr) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Expected format '" << Format_Name(Format::STRING)
               << "', but got '" << absl::AsciiStrToUpper(format_case_name)
               << "' instead.";
      }
      break;
    }
    case Format::HEX_STRING: {
      if (format_case != IrValue::kHexStr) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Expected format '" << Format_Name(Format::HEX_STRING)
               << "', but got '" << absl::AsciiStrToUpper(format_case_name)
               << "' instead.";
      }
      std::string hex_str = ir_value.hex_str();
      if (absl::StartsWith(hex_str, "0x")) {
        hex_str.replace(0, 2, "");
      }
      break;
    }
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unexpected format: " << Format_Name(format);
  }

  return absl::OkStatus();
}

absl::StatusOr<std::string> IrValueToNormalizedByteString(
    const IrValue &ir_value, const int bitwidth) {
  switch (ir_value.format_case()) {
    case IrValue::kMac: {
      ASSIGN_OR_RETURN(auto mac, MacAddress::OfString(ir_value.mac()));
      return mac.ToPaddedByteString();
    }
    case IrValue::kIpv4: {
      ASSIGN_OR_RETURN(auto ipv4, Ipv4Address::OfString(ir_value.ipv4()));
      return ipv4.ToPaddedByteString();
    }
    case IrValue::kIpv6: {
      ASSIGN_OR_RETURN(auto ipv6, Ipv6Address::OfString(ir_value.ipv6()));
      return ipv6.ToPaddedByteString();
    }
    case IrValue::kStr:
      return ir_value.str();
    case IrValue::kHexStr: {
      const std::string &hex_str = ir_value.hex_str();
      const int expected_num_hex_chars =
          bitwidth / 4 + (bitwidth % 4 != 0 ? 1 : 0);
      if (!absl::StartsWith(hex_str, "0x")) {
        return gutil::InvalidArgumentErrorBuilder()
               << "IR Value '" << hex_str
               << "' with hex string format does not start with 0x.";
      }
      absl::string_view stripped_hex = absl::StripPrefix(hex_str, "0x");
      if (expected_num_hex_chars != stripped_hex.size()) {
        return gutil::InvalidArgumentErrorBuilder()
               << "IR Value '" << hex_str
               << "' has the wrong number of characters. Has " << hex_str.size()
               << " characters, but expected " << (expected_num_hex_chars + 2)
               << " instead.";
      }
      if (!std::all_of(stripped_hex.begin(), stripped_hex.end(),
                       [](const char c) {
                         return std::isxdigit(c) != 0 && c == std::tolower(c);
                       })) {
        return gutil::InvalidArgumentErrorBuilder()
               << "IR Value '" << hex_str
               << "' contains non-hexadecimal characters.";
      }

      std::string byte_string = absl::HexStringToBytes(
          absl::StrCat(stripped_hex.size() % 2 == 0 ? "" : "0", stripped_hex));
      return ArbitraryToNormalizedByteString(byte_string, bitwidth);
    }
    case IrValue::FORMAT_NOT_SET:
      break;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "Uninitialized value: " << ir_value.DebugString();
}

absl::StatusOr<IrValue> FormattedStringToIrValue(const std::string &value,
                                                 Format format) {
  IrValue result;
  switch (format) {
    case Format::MAC:
      result.set_mac(value);
      break;
    case Format::IPV4:
      result.set_ipv4(value);
      break;
    case Format::IPV6:
      result.set_ipv6(value);
      break;
    case Format::STRING:
      result.set_str(value);
      break;
    case Format::HEX_STRING:
      result.set_hex_str(value);
      break;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unexpected format: " << Format_Name(format);
  }
  return result;
}

absl::StatusOr<std::string> IrValueToFormattedString(const IrValue &value,
                                                     Format format) {
  switch (format) {
    case Format::MAC:
      return value.mac();
    case Format::IPV4:
      return value.ipv4();
    case Format::IPV6:
      return value.ipv6();
    case Format::STRING:
      return value.str();
    case Format::HEX_STRING:
      return value.hex_str();
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unexpected format: " << Format_Name(format);
  }
}

bool IsAllZeros(const std::string &s) {
  bool has_non_zero_value = false;
  for (const auto &c : s) {
    if (c != '\x00') {
      has_non_zero_value = true;
      break;
    }
  }

  return has_non_zero_value == false;
}

absl::StatusOr<std::string> Intersection(const std::string &left,
                                         const std::string &right) {
  if (left.size() != right.size()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Cannot find intersection. '" << absl::CEscape(left) << "'("
           << left.size() << " bytes) and '" << absl::CEscape(right) << "'("
           << right.size() << " bytes) are of unequal length.";
  }
  std::string result = "";
  for (int i = 0; i < left.size(); ++i) {
    char left_c = left[i];
    char right_c = right[i];
    result += (left_c & right_c);
  }
  return result;
}

absl::StatusOr<std::string> PrefixLenToMask(int prefix_len, int bitwidth) {
  if (prefix_len > bitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Prefix length " << prefix_len
           << " cannot be greater than bitwidth " << bitwidth << ".";
  }

  std::string result;
  if (bitwidth % 8) {
    int msb = bitwidth % 8;
    result += (0xff >> (kNumBitsInByte - msb) & 0xff);
    prefix_len -= msb;
    bitwidth -= msb;
  }
  for (int i = bitwidth; i > 0; i -= kNumBitsInByte) {
    if (prefix_len >= (int)kNumBitsInByte) {
      result += '\xff';
    } else {
      if (prefix_len > 0) {
        result += (0xff << (kNumBitsInByte - prefix_len) & 0xff);
      } else {
        result += '\x00';
      }
    }
    prefix_len -= kNumBitsInByte;
  }
  return result;
}

absl::Status IsGoogleRpcCode(int rpc_code) {
  if (rpc_code < 0 || rpc_code > 15) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid status code: " << rpc_code << ".";
  }
  return absl::OkStatus();
}

absl::Status ValidateGenericUpdateStatus(google::rpc::Code code,
                                         const std::string &message) {
  if (code == google::rpc::OK && !message.empty()) {
    return absl::InvalidArgumentError(
        "OK status should not contain error message.");
  }
  return absl::OkStatus();
}

std::string IrWriteResponseToReadableMessage(
    const IrWriteResponse &ir_write_response) {
  std::string readable_message;
  absl::StrAppend(&readable_message, "Batch failed, individual results:\n");
  int i = 1;
  for (const auto &ir_update_status : ir_write_response.statuses()) {
    absl::StrAppend(&readable_message, "#", i, ": ",
                    absl::StatusCodeToString(static_cast<absl::StatusCode>(
                        ir_update_status.code())));
    if (!ir_update_status.message().empty()) {
      absl::StrAppend(&readable_message, ": ", ir_update_status.message(),
                      "\n");
    } else {
      // Insert a new line for OK status.
      absl::StrAppend(&readable_message, "\n");
    }
    ++i;
  }

  return readable_message;
}

std::string GenerateFormattedError(absl::string_view field,
                                   absl::string_view error_string) {
  const std::vector<absl::string_view> errors =
      absl::StrSplit(error_string, '\n');
  if (errors.size() == 1) {
    std::string error = std::string(error_string);
    if (absl::StartsWith(error, kNewBullet)) {
      error = error.erase(0, 2);
    }
    return absl::StrCat(field, " is invalid: ", error);
  }
  return absl::StrCat(field, " is invalid for the following reasons:\n",
                      kIndent,
                      absl::StrJoin(errors, absl::StrCat("\n", kIndent)));
}

std::string GenerateReason(absl::string_view entity_name,
                           absl::string_view error_message) {
  return absl::StrCat(kNewBullet, entity_name, ": ", error_message);
}

std::string TableName(absl::string_view table_name) {
  return absl::StrCat("Table entry for '", table_name, "'");
}

std::string MatchFieldName(absl::string_view match_name) {
  return absl::StrCat("Match field '", match_name, "'");
}

std::string ActionName(absl::string_view action_name) {
  return absl::StrCat("Action '", action_name, "'");
}

std::string ParamName(absl::string_view param_name) {
  return absl::StrCat("Param '", param_name, "'");
}
std::string MetadataName(absl::string_view metadata_name) {
  return absl::StrCat("Metadata '", metadata_name, "'");
}

}  // namespace pdpi

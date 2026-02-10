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

#include "sai_p4/instantiations/google/test_tools/table_entry_generator_helper.h"

#include <string>

#include "absl/functional/bind_front.h"
#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/netaddr/ipv4_address.h"
#include "p4_infra/p4_pdpi/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/netaddr/mac_address.h"

namespace sai {
namespace {
using ::p4::config::v1::MatchField;

bool IsIteratingFormat(pdpi::Format format) {
  // This is just !STRING today, but use a switch for forward-compatibility.
  switch (format) {
    case pdpi::Format::IPV4:
    case pdpi::Format::IPV6:
    case pdpi::Format::MAC:
    case pdpi::Format::HEX_STRING:
      return true;
    default:
      break;
  }
  return false;
}

// Returns the Nth incremental IPv4 address.
netaddr::Ipv4Address NthIpv4Address(int i) {
  constexpr uint32_t kBaseIpv4 = 0x10000000;
  return netaddr::Ipv4Address(std::bitset<32>(kBaseIpv4 + i));
}

// Returns the Nth incremental IPv6 address.
netaddr::Ipv6Address NthIpv6Address(int i) {
  constexpr int64_t kBaseIpv6 = 0x1234000000000000;
  return netaddr::Ipv6Address(absl::MakeUint128(kBaseIpv6 + i, 0));
}

// Returns the Nth incremental Mac address.
netaddr::MacAddress NthMacAddress(int i) {
  constexpr int64_t kBaseMac = 0xAA0000000000;
  return netaddr::MacAddress(std::bitset<48>(kBaseMac + i));
}

// Returns the Nth incremental hex string. Wraps around based on bitwidth.
std::string NthHexString(int bitwidth, int i) {
  int hex_width = (bitwidth + 3) / 4;  // Round up
  // Range is [1, 2^bitwidth-1]
  uint32_t int_value =
      bitwidth >= 32 ? i + 1u : i % ((1ull << bitwidth) - 1) + 1;
  std::string hex_value = absl::StrFormat("%x", int_value);
  std::string value =
      absl::StrCat("0x",
                   hex_width > hex_value.size()  // add front zero padding
                       ? std::string(hex_width - hex_value.size(), '0')
                       : "",
                   hex_value);
  return value;
}

// Returns the prefix length for LPM matches.
int PrefixLength(pdpi::Format format, int bitwidth) {
  switch (format) {
    case pdpi::Format::IPV4:
      return 32;
    case pdpi::Format::IPV6:
      return 64;  // To maintain compatibility with 64-bit IPv6 match fields.
    case pdpi::Format::MAC:
      return 48;
    case pdpi::Format::HEX_STRING:
      return bitwidth;
    default:
      break;
  }
  LOG(FATAL)  // Crash OK
      << "Cannot form LPM match of type " << pdpi::Format_Name(format);
  return -1;
}

// Populates a pdpi::Irvalue with the Nth incremental value.
void PopulateNthValue(pdpi::IrValue* value, pdpi::Format format, int bitwidth,
                      int i) {
  switch (format) {
    case pdpi::Format::IPV4:
      value->set_ipv4(NthIpv4Address(i).ToString());
      break;
    case pdpi::Format::IPV6:
      value->set_ipv6(NthIpv6Address(i).ToString());
      break;
    case pdpi::Format::MAC:
      value->set_mac(NthMacAddress(i).ToString());
      break;
    case pdpi::Format::HEX_STRING:
      value->set_hex_str(NthHexString(bitwidth, i));
      break;
    default:
      LOG(FATAL)  // Crash OK
          << "Cannot form value of type " << pdpi::Format_Name(format);
      break;
  }
}

// Returns a full hex string mask for a field of the given bitwidth.
std::string FullMask(int bitwidth) {
  int f_count = 0;
  while (bitwidth >= 4) {
    ++f_count;
    bitwidth -= 4;
  }
  if (bitwidth == 0) return absl::StrCat("0x", std::string(f_count, 'f'));
  return absl::StrCat("0x", (1 << bitwidth) - 1, std::string(f_count, 'f'));
}

// Populates the largest appropriate mask value for the provided format.
void PopulateMask(pdpi::IrValue* mask, pdpi::Format format, int bitwidth) {
  switch (format) {
    case pdpi::Format::IPV4:
      mask->set_ipv4(netaddr::Ipv4Address::AllOnes().ToString());
      break;
    case pdpi::Format::IPV6:
      mask->set_ipv6(netaddr::Ipv6Address::Upper64BitMask().ToString());
      break;
    case pdpi::Format::MAC:
      mask->set_mac(netaddr::MacAddress::AllOnes().ToString());
      break;
    case pdpi::Format::HEX_STRING:
      mask->set_hex_str(FullMask(bitwidth));
      break;
    default:
      LOG(FATAL)  // Crash OK
          << "Cannot form mask of type " << pdpi::Format_Name(format);
      break;
  }
}

// Prepares a match field for population by iteration functions.
// Initializes the match field name.
// Creates the iterating pdpi::IrValue.
// Creates and initializes the appropriate mask or LPM.
pdpi::IrMatch PrepareIteratingMatchField(
    const pdpi::IrMatchFieldDefinition& match_definition) {
  pdpi::IrMatch match;
  match.set_name(match_definition.match_field().name());
  pdpi::Format format = match_definition.format();
  int bitwidth = match_definition.match_field().bitwidth();

  switch (match_definition.match_field().match_type()) {
    case MatchField::EXACT:
      match.mutable_exact();
      break;
    case MatchField::OPTIONAL:
      match.mutable_optional()->mutable_value();
      break;
    case MatchField::LPM:
      match.mutable_lpm()->mutable_value();
      match.mutable_lpm()->set_prefix_length(PrefixLength(format, bitwidth));
      break;
    case MatchField::TERNARY:
      match.mutable_ternary()->mutable_value();
      PopulateMask(match.mutable_ternary()->mutable_mask(), format, bitwidth);
      break;
    default:
      LOG(FATAL)  // Crash OK
          << "Unable to generate match field with format type "
          << pdpi::Format_Name(format);
      break;
  }
  return match;
}

// Returns a copy of the table entry with the last match field containing the
// Nth iterating value.
pdpi::IrTableEntry LastMatchFieldGenerator(MatchField::MatchType match_type,
                                           pdpi::Format format, int bitwidth,
                                           pdpi::IrTableEntry entry, int i) {
  pdpi::IrMatch& match = *entry.mutable_matches()->rbegin();
  switch (match_type) {
    case MatchField::EXACT:
      PopulateNthValue(match.mutable_exact(), format, bitwidth, i);
      break;
    case MatchField::OPTIONAL:
      PopulateNthValue(match.mutable_optional()->mutable_value(), format,
                       bitwidth, i);
      break;
    case MatchField::LPM:
      PopulateNthValue(match.mutable_lpm()->mutable_value(), format, bitwidth,
                       i);
      break;
    case MatchField::TERNARY:
      PopulateNthValue(match.mutable_ternary()->mutable_value(), format,
                       bitwidth, i);
      break;
    default:
      LOG(FATAL)  // Crash OK
          << "Unable to generate match field with format '"
          << pdpi::Format_Name(format) << "' (" << format << ")";
  }
  return entry;
}

// Generates the Nth iterating match field from the provided properties and
// iterates the entry priority.
pdpi::IrTableEntry LastMatchFieldAndPriorityGenerator(
    MatchField::MatchType match_type, pdpi::Format format, int bitwidth,
    pdpi::IrTableEntry entry, int i) {
  entry = LastMatchFieldGenerator(match_type, format, bitwidth,
                                  std::move(entry), i);
  entry.set_priority(i + 1);  // Don't set a priority of 0.
  return entry;
}

// Returns an EntryGenerator based on the input table definition. Adds an
// iterating match field and optional iterating priority.
TableEntryGenerator::EntryGenerator IrMatchFieldGenerator(
    const pdpi::IrTableDefinition& table_definition,
    pdpi::IrTableEntry base_entry, absl::string_view match_field,
    bool iterate_priority) {
  auto match_definition_iter =
      table_definition.match_fields_by_name().find(match_field);
  if (match_definition_iter == table_definition.match_fields_by_name().end()) {
    LOG(FATAL)  // Crash OK
        << "Unable to find match field '" << match_field
        << "' in IrTableDefinition for '" << table_definition.preamble().alias()
        << "'.";
  }
  const pdpi::IrMatchFieldDefinition& match_definition =
      match_definition_iter->second;

  // This is just STRING today, but use switch for forward-compatibility.
  if (!IsIteratingFormat(match_definition.format())) {
    LOG(FATAL)  // Crash OK
        << "Unable to generate match field with format type "
        << pdpi::Format_Name(match_definition.format());
  }
  if (match_definition.format() == pdpi::Format::HEX_STRING &&
      match_definition.match_field().bitwidth() == 0) {
    LOG(FATAL)  // Crash OK
        << "Unable to generate HEX_STRING match field of bitwidth 0.";
  }
  for (const auto& base_match : base_entry.matches()) {
    if (base_match.name() == match_field) {
      LOG(FATAL)  // Crash OK
          << "Match field '" << match_field
          << "' is already defined in the base entry. Cannot create "
          << "generator for '" << match_field << "'.";
    }
  }

  *base_entry.add_matches() = PrepareIteratingMatchField(match_definition);
  if (iterate_priority) {
    return absl::bind_front(
        LastMatchFieldAndPriorityGenerator,
        match_definition.match_field().match_type(), match_definition.format(),
        match_definition.match_field().bitwidth(), base_entry);
  } else {
    return absl::bind_front(
        LastMatchFieldGenerator, match_definition.match_field().match_type(),
        match_definition.format(), match_definition.match_field().bitwidth(),
        base_entry);
  }
}

// Returns a copy of the input table entry with the priority field set to the
// Nth value.
pdpi::IrTableEntry IncrementPriority(pdpi::IrTableEntry entry, int i) {
  entry.set_priority(i + 1);  // Don't set a priority of 0.
  return entry;
}
}  // namespace

TableEntryGenerator::EntryGenerator IrMatchFieldGenerator(
    const pdpi::IrTableDefinition& table_definition,
    pdpi::IrTableEntry base_entry, absl::string_view match_field) {
  return IrMatchFieldGenerator(table_definition, base_entry, match_field,
                               false);
}

TableEntryGenerator::EntryGenerator IrMatchFieldAndPriorityGenerator(
    const pdpi::IrTableDefinition& table_definition,
    pdpi::IrTableEntry base_entry, absl::string_view match_field) {
  return IrMatchFieldGenerator(table_definition, base_entry, match_field, true);
}

TableEntryGenerator::EntryGenerator PriorityGenerator(
    pdpi::IrTableEntry base_entry) {
  return absl::bind_front(IncrementPriority, base_entry);
}

}  // namespace sai

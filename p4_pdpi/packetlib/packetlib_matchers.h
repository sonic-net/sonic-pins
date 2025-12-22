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

#ifndef PINS_P4_PDPI_PACKETLIB_PACKETLIB_MATCHERS_H_
#define PINS_P4_PDPI_PACKETLIB_PACKETLIB_MATCHERS_H_

#include "gutil/proto_matchers.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace packetlib {

// gMock matcher that checks if its argument, a `packetlib::Header`, is of the
// given `header_case`.
// That is, checks that `argument.header_case() == header_case`.
//
// Sample usage:
// ```
//   EXPECT_THAT(ipv4_packet.headers(),
//               ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
//                           HasHeaderCase(packetlib::Header::kIpv4Header)));
// ```
inline gutil::HasOneofCaseMatcher<Header>
HasHeaderCase(Header::HeaderCase header_case) {
  return gutil::HasOneofCaseMatcher<Header>("header", header_case);
}

} // namespace packetlib

#endif // PINS_P4_PDPI_PACKETLIB_PACKETLIB_MATCHERS_H_

// Copyright 2021 Google LLC
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
#ifndef GOOGLE_P4_FUZZER_FUZZER_CONFIG_H_
#define GOOGLE_P4_FUZZER_FUZZER_CONFIG_H_

#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {

struct FuzzerConfig {
  // The IrP4Info of the program to be fuzzed.
  pdpi::IrP4Info info;
  // The set of valid port names.
  std::vector<std::string> ports;
  // The set of valid QOS queues.
  std::vector<std::string> qos_queues;
  // The P4RT role the fuzzer should use.
  std::string role;
};

}  // namespace p4_fuzzer

#endif  // GOOGLE_P4_FUZZER_FUZZER_CONFIG_H_

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

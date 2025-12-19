// Given the instantiation and target platform, this binary outputs the probuf
// text string of the forwarding pipeline config to stdout.

#include <iostream>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "gutil/proto.h"
#include "p4/v1/p4runtime.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"

ABSL_FLAG(sai::Instantiation, instantiation, sai::Instantiation::kMiddleblock,
          "The switch (SAI) instantiation.");
ABSL_FLAG(sai::NonstandardPlatform, platform, sai::NonstandardPlatform::kBmv2,
          "The (non-standard) target platform.");

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  const p4::v1::ForwardingPipelineConfig config =
      GetNonstandardForwardingPipelineConfig(absl::GetFlag(FLAGS_instantiation),
                                             absl::GetFlag(FLAGS_platform));
  std::cout << gutil::PrintTextProto(config);

  return 0;
}

#ifndef PINS_SAI_P4_INSTANTIATIONS_GOOGLE_SAI_NONSTANDARD_PLATFORMS_H_
#define PINS_SAI_P4_INSTANTIATIONS_GOOGLE_SAI_NONSTANDARD_PLATFORMS_H_

#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {

enum class NonstandardPlatform {
  kBmv2,
  kP4Symbolic,
};

inline absl::flat_hash_map<NonstandardPlatform, std::string>
NonstandardPlatformNames() {
  return {
      {NonstandardPlatform::kBmv2, "bmv2"},
      {NonstandardPlatform::kP4Symbolic, "p4_symbolic"},
  };
}

// Returns a vector of all nonstandard platforms.
inline std::vector<NonstandardPlatform> AllNonstandardPlatforms() {
  const auto platform_names = NonstandardPlatformNames();
  std::vector<NonstandardPlatform> platforms;
  platforms.reserve(platform_names.size());
  for (const auto& p : platform_names) platforms.push_back(p.first);
  return platforms;
}

// Parses an NonstandardPlatform from the command line flag value
// `platform_name`. Returns true and sets `*platform` on success;
// returns false and sets `*error` on failure.
// See https://abseil.io/docs/cpp/guides/flags#validating-flag-values for more
// information.
bool AbslParseFlag(absl::string_view platform_name,
                   NonstandardPlatform* platform, std::string* error);

// Returns a textual flag value corresponding to the given platform.
std::string AbslUnparseFlag(NonstandardPlatform platform);

// Returns the name of the given platform.
std::string PlatformName(NonstandardPlatform platform);

// Returns JSON config for the SAI P4 program for the given platform.
std::string GetNonstandardP4Config(Instantiation instantiation,
                                   NonstandardPlatform platform);

// Returns P4 Info for the SAI P4 program for the given platform.
p4::config::v1::P4Info GetNonstandardP4Info(Instantiation instantiation,
                                            NonstandardPlatform platform);

// Returns a `ForwardingPipelineConfig` for the SAI P4 program for the given
// platform.
p4::v1::ForwardingPipelineConfig
GetNonstandardForwardingPipelineConfig(Instantiation instantiation,
                                       NonstandardPlatform platform);

// Returns the file name of the preprocessed P4 program for the given
// instantiation and platform.
std::string PreprocessedInstantiationFileName(
    Instantiation role,
    std::optional<NonstandardPlatform> nonstandard_platform);

// Returns the file name of the preprocessed P4 program for the given
// instantiation and platform.
std::string PreprocessedInstantiationFileName(
    Instantiation role,
    std::optional<NonstandardPlatform> nonstandard_platform);

}  // namespace sai

#endif // PINS_SAI_P4_INSTANTIATIONS_GOOGLE_SAI_NONSTANDARD_PLATFORMS_H_

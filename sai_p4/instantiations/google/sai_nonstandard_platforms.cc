#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"

#include <algorithm>
#include <optional>
#include <string>

#include "absl/log/check.h"
#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "google/protobuf/text_format.h"
#include "p4/config/v1/p4info.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms_embed.h"

namespace sai {

namespace {

using ::p4::config::v1::P4Info;

// Return the base (no suffix) name of the instantiation p4info file.
std::string InstantiationName(Instantiation instantiation) {
  return InstantiationToString(instantiation);
}

// Return the name of the P4Config JSON file.
std::string P4ConfigName(Instantiation instantiation, NonstandardPlatform platform) {
  return absl::StrFormat("sai_%s_%s.config.json",  InstantiationName(instantiation),
                         PlatformName(platform));
}

// Return the name of the P4Info protobuf file.
std::string P4InfoName(Instantiation instantiation, NonstandardPlatform platform) {
  return absl::StrFormat("sai_%s_%s.p4info.pb.txt",  InstantiationName(instantiation),
                         PlatformName(platform));
}

}  // namespace

bool AbslParseFlag(absl::string_view platform_name,
                   NonstandardPlatform* platform, std::string* error) {
  const auto platform_names = NonstandardPlatformNames();
  const auto it =
      std::find_if(platform_names.begin(), platform_names.end(),
                   [=](auto& p) { return p.second == platform_name; });
  if (it == platform_names.end()) {
    absl::StrAppend(error, "unknown platform name: '", platform_name, "'");
    return false;
  }

  *platform = it->first;
  return true;
}

std::string AbslUnparseFlag(NonstandardPlatform platform) {
  const auto platform_names = NonstandardPlatformNames();
  if (!platform_names.contains(platform)) {
    LOG(DFATAL) << "Invalid NonstandardPlattform: "
                << static_cast<int>(platform);
    return "<invalid-platform>";
  }

  return platform_names.at(platform);
}

std::string PlatformName(NonstandardPlatform platform) {
  return AbslUnparseFlag(platform);
}

std::string GetNonstandardP4Config(Instantiation instantiation,
                                   NonstandardPlatform platform) {
  const gutil::FileToc* toc = sai_nonstandard_platforms_embed_create();
  std::string key = P4ConfigName(instantiation, platform);
  for (int i = 0; i < sai_nonstandard_platforms_embed_size(); ++i) {
    if (toc[i].name == key) return std::string(toc[i].data);
  }
  LOG(DFATAL) << "couldn't find P4 config for instantiation '"
              << InstantiationToString(instantiation) << "' and platform '"
              << PlatformName(platform) << "': key '" << key << "'"
              << " not found in table of contents";
  return "";
}

P4Info GetNonstandardP4Info(Instantiation instantiation, NonstandardPlatform platform) {
  P4Info p4info;
  const gutil::FileToc* toc = sai_nonstandard_platforms_embed_create();
  std::string key = P4InfoName(instantiation, platform);
  for (int i = 0; i < sai_nonstandard_platforms_embed_size(); ++i) {
    if (toc[i].name == key) {
      CHECK(  // Crash ok: TAP rules out failures.
          google::protobuf::TextFormat::ParseFromString(toc[i].data, &p4info))
          << "unable to parse embedded P4 info file '" << key
          << "': " << toc[i].data;
      return p4info;
    }
  }
  LOG(DFATAL) << "couldn't find P4 info for instantiation '" << InstantiationToString(instantiation)
              << "' and platform '" << PlatformName(platform) << "': key '"
              << key << "'"
              << " not found in table of contents";
  return p4info;
}

p4::v1::ForwardingPipelineConfig GetNonstandardForwardingPipelineConfig(
    Instantiation instantiation, NonstandardPlatform platform) {
  p4::v1::ForwardingPipelineConfig config;
  *config.mutable_p4_device_config() =
      GetNonstandardP4Config(instantiation, platform);
  *config.mutable_p4info() = GetNonstandardP4Info(instantiation, platform);
  return config;
}

std::string PreprocessedInstantiationFileName(
    Instantiation role,
    std::optional<NonstandardPlatform> nonstandard_platform) {
  return "preprocessed_" +
         (nonstandard_platform.has_value()
              ? PlatformName(nonstandard_platform.value())
              : "standard") +
         "_" + InstantiationName(role) + ".p4";
}

}  // namespace sai

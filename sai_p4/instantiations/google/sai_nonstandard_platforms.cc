#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"

#include "absl/strings/str_format.h"
#include "glog/logging.h"
#include "google/protobuf/text_format.h"
#include "p4/config/v1/p4info.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms_embed.h"

namespace sai {

namespace {

using ::p4::config::v1::P4Info;

std::string P4ConfigName(Instantiation instantiation, NonstandardPlatform platform) {
  return absl::StrFormat("sai_%s_%s.config.json", InstantiationToString(instantiation),
                         PlatformName(platform));
}

std::string P4infoName(Instantiation instantiation, NonstandardPlatform platform) {
  return absl::StrFormat("sai_%s_%s.p4info.pb.txt", InstantiationToString(instantiation),
                         PlatformName(platform));
}

}  // namespace

std::string PlatformName(NonstandardPlatform platform) {
  switch (platform) {
    case NonstandardPlatform::kBmv2:
      return "bmv2";
    case NonstandardPlatform::kP4Symbolic:
      return "p4_symbolic";
  }
  LOG(DFATAL) << "invalid NonstandardPlattform: " << static_cast<int>(platform);
  return "";
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
  std::string key = P4infoName(instantiation, platform);
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

}  // namespace sai

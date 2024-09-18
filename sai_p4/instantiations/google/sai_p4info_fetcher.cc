#include "sai_p4/instantiations/google/sai_p4info_fetcher.h"

#include <optional>

#include "absl/log/check.h"
#include "google/protobuf/text_format.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/clos_stage.h"
#include "sai_p4/instantiations/google/fabric_border_router_p4info_embed.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/middleblock_p4info_embed.h"
#include "sai_p4/instantiations/google/tor_p4info_embed.h"
#include "sai_p4/instantiations/google/unioned_p4info_embed.h"
#include "sai_p4/instantiations/google/wbb_p4info_embed.h"

namespace sai {
namespace {
using ::google::protobuf::TextFormat;
using ::gutil::FileToc;
using ::p4::config::v1::P4Info;

P4Info FileTocToP4Info(const FileToc* const toc) {
  std::string data(toc[0].data, toc[0].size);
  P4Info info;
  CHECK(  // Crash ok: TAP rules out failures.
      TextFormat::ParseFromString(data, &info))
      << "unable to read embedded p4info text file";
  return info;
}

// Returns the middleblock P4Info at the provided stage. If the stage is not
// defined, returns the stage 2 P4Info by default.
P4Info MiddleblockP4Info(std::optional<ClosStage> stage) {
  if (stage.has_value()) {
    switch (*stage) {
      case ClosStage::kStage2:
        return FileTocToP4Info(
            middleblock_p4info_embed_create());
      case ClosStage::kStage3:
        return FileTocToP4Info(
            middleblock_p4info_embed_create());
    }
  }
  return FileTocToP4Info(
      middleblock_p4info_embed_create());
}

// Returns the fabric border router P4Info at the provided stage. If the stage
// is not defined, returns the stage 2 P4Info by default.
P4Info FabricBorderRouterP4Info(std::optional<ClosStage> stage) {
  if (stage.has_value()) {
    switch (*stage) {
      case ClosStage::kStage2:
        return FileTocToP4Info(
            fabric_border_router_p4info_embed_create());
      case ClosStage::kStage3:
        return FileTocToP4Info(
            fabric_border_router_p4info_embed_create());
    }
  }
  return FileTocToP4Info(
      fabric_border_router_p4info_embed_create());
}

}  // namespace

P4Info FetchP4Info(Instantiation instantiation,
                   std::optional<ClosStage> stage) {
  P4Info p4info;
  switch (instantiation) {
    case Instantiation::kMiddleblock:
      p4info = MiddleblockP4Info(stage);
      break;
    case Instantiation::kFabricBorderRouter:
      p4info = FabricBorderRouterP4Info(stage);
      break;
    case Instantiation::kTor:
      p4info = FileTocToP4Info(tor_p4info_embed_create());
      break;
    case Instantiation::kWbb:
      p4info = FileTocToP4Info(wbb_p4info_embed_create());
      break;
  }
  return p4info;
}

P4Info FetchUnionedP4Info() {
  return FileTocToP4Info(unioned_p4info_embed_create());
}

}  // namespace sai

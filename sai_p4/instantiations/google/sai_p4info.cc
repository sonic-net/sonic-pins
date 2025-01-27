#include "sai_p4/instantiations/google/sai_p4info.h"

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "glog/logging.h"
#include "google/protobuf/text_format.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info_fetcher.h"
#include "sai_p4/tools/p4info_tools.h"

namespace sai {

using ::p4::config::v1::P4Info;
using ::pdpi::IrP4Info;

namespace {

IrP4Info* CreateIrP4Info(const P4Info& info) {
  absl::StatusOr<IrP4Info> ir_p4info = pdpi::CreateIrP4Info(info);
  CHECK(ir_p4info.status().ok())  // Crash ok: TAP rules out failures.
      << ir_p4info.status();
  return new IrP4Info(std::move(ir_p4info).value());
}

}  // namespace

const P4Info& GetP4Info(Instantiation instantiation) {
  static const P4Info* const kFabricBorderRouterP4Info =
      new P4Info(FetchP4Info(Instantiation::kFabricBorderRouter));
  static const P4Info* const kMiddleblockP4Info =
      new P4Info(FetchP4Info(Instantiation::kMiddleblock));
  static const P4Info* const kTopOfRackP4Info =
      new P4Info(FetchP4Info(Instantiation::kTor));
  static const P4Info* const kWbbP4Info =
      new P4Info(FetchP4Info(Instantiation::kWbb));

  switch (instantiation) {
    case Instantiation::kFabricBorderRouter:
      return *kFabricBorderRouterP4Info;
    case Instantiation::kMiddleblock:
      return *kMiddleblockP4Info;
    case Instantiation::kTor:
      return *kTopOfRackP4Info;
    case Instantiation::kWbb:
      return *kWbbP4Info;
  }
  LOG(DFATAL) << "Obtaining P4Info for invalid instantiation: "
              << static_cast<int>(instantiation);

  static const P4Info* const kEmptyP4Info = new P4Info();
  return *kEmptyP4Info;
}

P4Info GetP4InfoWithHashSeed(Instantiation instantiation, uint32_t seed) {
  P4Info p4info = GetP4Info(instantiation);
  SetSaiHashSeed(p4info, seed);
  return p4info;
}

const IrP4Info& GetIrP4Info(Instantiation instantiation) {
  static const IrP4Info* const kFabricBorderRouterIrP4Info =
      CreateIrP4Info(GetP4Info(Instantiation::kFabricBorderRouter));
  static const IrP4Info* const kMiddleblockIrP4Info =
      CreateIrP4Info(GetP4Info(Instantiation::kMiddleblock));
  static const IrP4Info* const kTorIrP4Info =
      CreateIrP4Info(GetP4Info(Instantiation::kTor));
  static const IrP4Info* const kWbbIrP4Info =
      CreateIrP4Info(GetP4Info(Instantiation::kWbb));

  switch (instantiation) {
    case Instantiation::kFabricBorderRouter:
      return *kFabricBorderRouterIrP4Info;
    case Instantiation::kMiddleblock:
      return *kMiddleblockIrP4Info;
    case Instantiation::kTor:
      return *kTorIrP4Info;
    case Instantiation::kWbb:
      return *kWbbIrP4Info;
  }
  LOG(DFATAL) << "Obtaining P4Info for invalid instantiation: "
              << static_cast<int>(instantiation);
  static const IrP4Info* const kEmptyIrP4Info = new IrP4Info();
  return *kEmptyIrP4Info;
}

const p4::config::v1::P4Info& GetUnionedP4Info() {
  static const P4Info* const unioned_p4info = new P4Info(FetchUnionedP4Info());
  return *unioned_p4info;
}

const IrP4Info& GetUnionedIrP4Info() {
  static const IrP4Info* const kUnionedIrP4Info =
      CreateIrP4Info(GetUnionedP4Info());
  return *kUnionedIrP4Info;
}

}  // namespace sai

#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"

#include "absl/status/statusor.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"
#include "sai_p4/tools/auxiliary_entries_for_v1model_targets.h"

namespace sai {

using ::Experimental::p4::test::Bmv2;
using ::p4::v1::ForwardingPipelineConfig;

absl::StatusOr<Bmv2> SetUpBmv2ForSaiP4(
    const ForwardingPipelineConfig& bmv2_config, Bmv2::Args bmv2_args) {
  ASSIGN_OR_RETURN(Bmv2 bmv2, Bmv2::Create(std::move(bmv2_args)));
  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      &bmv2.P4RuntimeSession(),
      p4::v1::SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT,
      bmv2_config));
  RETURN_IF_ERROR(pdpi::InstallPiEntity(
      &bmv2.P4RuntimeSession(),
      MakeV1modelPacketReplicationEngineEntryRequiredForPunts()));
  return bmv2;
}

absl::StatusOr<Bmv2> SetUpBmv2ForSaiP4(Instantiation instantiation,
                                       Bmv2::Args bmv2_args) {
  return SetUpBmv2ForSaiP4(GetNonstandardForwardingPipelineConfig(
                               instantiation, NonstandardPlatform::kBmv2),
                           std::move(bmv2_args));
}

}  // namespace sai

#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"

#include <bitset>
#include <string>
#include <utility>
#include <vector>

#include "absl/log/check.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/types/optional.h"
#include "gutil/status.h"
#include "gutil/version.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/p4_runtime_session_extras.pb.h"
#include "p4_pdpi/string_encodings/byte_string.h"
#include "p4_pdpi/string_encodings/hex_string.h"
#include "p4_pdpi/translation_options.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/fixed/ids.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"
#include "sai_p4/instantiations/google/versions.h"
#include "sai_p4/tools/auxiliary_entries_for_v1model_targets.h"

namespace sai {

using ::orion::p4::test::Bmv2;
using ::orion::p4::test::Bmv2Args;
using ::p4::v1::ForwardingPipelineConfig;
constexpr int kV1ModelPortBitwidth = 9;
constexpr int kV1ModelCloneSessionBitwidth = 32;

namespace {

// Convenience struct corresponding to p4::v1::Replica in p4runtime.proto.
struct ReplicaArgs {
  std::string port;
  int instance;
};

// Convenience struct corresponding to match fields in
// ingress_clone_table_entry.
struct IngressCloneMatchFields {
  bool marked_to_copy;
  // marked_to_mirror is omitted; presence or absence of `mirror_egress_port`
  // determines the value of marked_to_mirror.
  int clone_session;
  absl::optional<int> mirror_egress_port;
};

std::string V1ModelPortToP4RuntimeByteString(int port) {
  CHECK(port >= 0 && port < (1 << kV1ModelPortBitwidth));  // Crash ok.
  return pdpi::BitsetToP4RuntimeByteString<kV1ModelPortBitwidth>(port);
}

std::string V1ModelPortToHexString(int port) {
  CHECK(port >= 0 && port < (1 << kV1ModelPortBitwidth));  // Crash ok.
  return pdpi::BitsetToHexString<kV1ModelPortBitwidth>(port);
}

std::string CloneSessionToHexString(int clone_session) {
  CHECK(clone_session >= 0 &&  // Crash ok.
        clone_session < (1UL << kV1ModelCloneSessionBitwidth));
  return pdpi::BitsetToHexString<kV1ModelCloneSessionBitwidth>(clone_session);
}

// Creates p4::v1::Entity of CloneSessionEntry entry with Replicas created by
// `replica_args`.
p4::v1::Entity CloneSessionEntry(int clone_session,
                                 std::vector<ReplicaArgs> replica_args) {
  p4::v1::Entity entity;
  p4::v1::CloneSessionEntry& clone_session_entry =
      *entity.mutable_packet_replication_engine_entry()
           ->mutable_clone_session_entry();
  clone_session_entry.set_session_id(clone_session);
  for (const ReplicaArgs& replica_arg : replica_args) {
    p4::v1::Replica& replica = *clone_session_entry.add_replicas();
    replica.set_port(replica_arg.port);
    replica.set_instance(replica_arg.instance);
  }
  return entity;
}

absl::StatusOr<p4::v1::Entity> SaiP4IngressCloneTableEntry(
    const pdpi::IrP4Info& ir_p4info,
    IngressCloneMatchFields ingress_clone_match_fields) {
  bool marked_to_mirror =
      ingress_clone_match_fields.mirror_egress_port.has_value();

  pdpi::IrEntity ir_entity;
  pdpi::IrTableEntry& ir_table_entry = *ir_entity.mutable_table_entry();
  *ir_table_entry.mutable_table_name() = "ingress_clone_table";
  {
    pdpi::IrMatch* match = ir_table_entry.add_matches();
    *match->mutable_name() = "marked_to_copy";
    *match->mutable_exact()->mutable_hex_str() =
        ingress_clone_match_fields.marked_to_copy ? "0x1" : "0x0";
  }
  {
    pdpi::IrMatch* match = ir_table_entry.add_matches();
    *match->mutable_name() = "marked_to_mirror";
    *match->mutable_exact()->mutable_hex_str() =
        marked_to_mirror ? "0x1" : "0x0";
  }
  if (ingress_clone_match_fields.mirror_egress_port.has_value()) {
    pdpi::IrMatch* match = ir_table_entry.add_matches();
    *match->mutable_name() = "mirror_egress_port";
    *match->mutable_optional()->mutable_value()->mutable_hex_str() =
        V1ModelPortToHexString(*ingress_clone_match_fields.mirror_egress_port);
  }

  *ir_table_entry.mutable_action()->mutable_name() = "ingress_clone";
  pdpi::IrActionInvocation::IrActionParam& param =
      *ir_table_entry.mutable_action()->add_params();
  param.set_name("clone_session");
  *param.mutable_value()->mutable_hex_str() =
      CloneSessionToHexString(ingress_clone_match_fields.clone_session);
  ir_table_entry.set_priority(1);

  ASSIGN_OR_RETURN(
      p4::v1::Entity pi_entity,
      pdpi::IrEntityToPi(ir_p4info, ir_entity,
                         // TODO: Remove allow_unsupported once
                         // ingress_clone table can be ignored by p4info
                         // schema verification.
                         pdpi::TranslationOptions{.allow_unsupported = true}));

  return pi_entity;
}

// Returns CloneSession (CS) entries and IngressClone (IC) entries that
// aggregate punting and mirroring's effect needed by V1Model targets such as
// BMv2:
// 1. one CS entry with 1 p4::v1::Replica for punting only.
// 2. one IC entry that lets marked_to_punt packets to get cloned using the CS
// created in step 1.
// 3. One CS entry for each port with one p4::v1::Replica that mirrors to that
// port.
// 4. One IC entry for each port. Each IC entry lets marked_to_mirror packets
// to get cloned with the CS entry for that port created in step 3.
// 5. One CS entry for each port with 2 p4::v1::Replicas. In each CS entry, One
// replica mirrors to that particular port and the other replica punts.
// 6. One IC entry for each port. Each IC entry lets marked_to_mirror and
// marked_to_punt packets to get cloned and punt with the CS entry for that port
// created in step 5.
//
// BMv2's port number ranges from 1 to 511 (V1Model uses 9 bits for port and
// BMv2 prohibits port to be 0).
absl::StatusOr<pdpi::PiEntities> GetEntitiesForClone(
    const pdpi::IrP4Info& ir_p4info) {
  pdpi::PiEntities entities;
  int next_clone_session = 1;

  // Punt-only CS and IC.
  {
    int clone_session = next_clone_session++;
    *entities.add_entities() = CloneSessionEntry(
        clone_session,
        {ReplicaArgs{
            .port = V1ModelPortToP4RuntimeByteString(SAI_P4_CPU_PORT),
            .instance = SAI_P4_REPLICA_INSTANCE_PACKET_IN,
        }});

    ASSIGN_OR_RETURN(*entities.add_entities(),
                     SaiP4IngressCloneTableEntry(
                         ir_p4info, IngressCloneMatchFields{
                                        .marked_to_copy = true,
                                        .clone_session = clone_session,
                                        .mirror_egress_port = std::nullopt,
                                    }));
  }

  // Mirror-only CSs and ICs.
  for (int mirror_egress_port = 1;
       mirror_egress_port < 1 << kV1ModelPortBitwidth; mirror_egress_port++) {
    int clone_session = next_clone_session++;
    *entities.add_entities() = CloneSessionEntry(
        clone_session,
        {ReplicaArgs{
            .port = V1ModelPortToP4RuntimeByteString(mirror_egress_port),
            .instance = SAI_P4_REPLICA_INSTANCE_MIRRORING}});

    ASSIGN_OR_RETURN(
        *entities.add_entities(),
        SaiP4IngressCloneTableEntry(
            ir_p4info, IngressCloneMatchFields{
                           .marked_to_copy = false,
                           .clone_session = clone_session,
                           .mirror_egress_port = mirror_egress_port,
                       }));
  }

  // Mirror-and-punt CSs and ICs.
  for (int mirror_egress_port = 1;
       mirror_egress_port < 1 << kV1ModelPortBitwidth; mirror_egress_port++) {
    int clone_session = next_clone_session++;
    *entities.add_entities() = CloneSessionEntry(
        clone_session,
        {
            ReplicaArgs{
                .port = V1ModelPortToP4RuntimeByteString(mirror_egress_port),
                .instance = SAI_P4_REPLICA_INSTANCE_MIRRORING},
            ReplicaArgs{
                .port = V1ModelPortToP4RuntimeByteString(SAI_P4_CPU_PORT),
                .instance = SAI_P4_REPLICA_INSTANCE_PACKET_IN},
        });
    ASSIGN_OR_RETURN(
        *entities.add_entities(),
        SaiP4IngressCloneTableEntry(
            ir_p4info, IngressCloneMatchFields{
                           .marked_to_copy = true,
                           .clone_session = clone_session,
                           .mirror_egress_port = mirror_egress_port,
                       }));
  }
  return entities;
}

}  // namespace

absl::StatusOr<Bmv2> SetUpBmv2ForSaiP4(
    const ForwardingPipelineConfig& bmv2_config,
    const SaiP4Bmv2SetupOptions& options, Bmv2Args bmv2_args) {
  ASSIGN_OR_RETURN(Bmv2 bmv2, Bmv2::Create(std::move(bmv2_args)));
  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      &bmv2.P4RuntimeSession(),
      p4::v1::SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT,
      bmv2_config));
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info,
                   pdpi::CreateIrP4Info(bmv2_config.p4info()));

  switch (options.initial_bmv2_control_plane) {
    case InitialBmv2ControlPlane::kNoControlPlane:
      return bmv2;
    case InitialBmv2ControlPlane::kInstallCloneEntries: {
      // TODO: Remove version checks and stop installing
      // PacketReplicationEngine entry for punt explicitly once the entire fleet
      // has moved to p4 programs that support ingress_cloning.
      ASSIGN_OR_RETURN(gutil::Version current_version,
                       gutil::ParseVersion(ir_p4info.pkg_info().version()));
      ASSIGN_OR_RETURN(gutil::Version version_with_ingress_cloning,
                       gutil::ParseVersion(
                           SAI_P4_PKGINFO_VERSION_HAS_INGRESS_CLONING_SUPPORT));
      if (current_version >= version_with_ingress_cloning) {
        ASSIGN_OR_RETURN(pdpi::PiEntities entities,
                         GetEntitiesForClone(ir_p4info));
        RETURN_IF_ERROR(
            pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), entities));
      } else {
        RETURN_IF_ERROR(pdpi::InstallPiEntity(
            &bmv2.P4RuntimeSession(),
            MakeV1modelPacketReplicationEngineEntryRequiredForPunts()));
      }
      return bmv2;
    }
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "Control plane configuration "
         << absl::StrCat(options.initial_bmv2_control_plane)
         << " is not covered.";
}

absl::StatusOr<Bmv2> SetUpBmv2ForSaiP4(Instantiation instantiation,
                                       const SaiP4Bmv2SetupOptions& options,
                                       Bmv2Args bmv2_args) {
  return SetUpBmv2ForSaiP4(GetNonstandardForwardingPipelineConfig(
                               instantiation, NonstandardPlatform::kBmv2),
                           options, std::move(bmv2_args));
}

}  // namespace sai

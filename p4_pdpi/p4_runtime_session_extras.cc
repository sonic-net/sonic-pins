#include "p4_pdpi/p4_runtime_session_extras.h"

#include "absl/algorithm/container.h"
#include "absl/status/status.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/table_entry_key.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/pd.h"

namespace pdpi {

absl::Status InstallPdTableEntries(
    P4RuntimeSession& p4rt, const google::protobuf::Message& pd_table_entries) {
  // Convert entries to PI representation.
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse config,
                   GetForwardingPipelineConfig(&p4rt));
  ASSIGN_OR_RETURN(IrP4Info info, CreateIrP4Info(config.config().p4info()));
  ASSIGN_OR_RETURN(std::vector<p4::v1::TableEntry> pi_entries,
                   PdTableEntriesToPi(info, pd_table_entries));

  // Install entries.
  return InstallPiTableEntries(&p4rt, info, pi_entries);
}

absl::Status InstallPdTableEntry(
    P4RuntimeSession& p4rt, const google::protobuf::Message& pd_table_entry) {
  // Convert entries to PI representation.
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse config,
                   GetForwardingPipelineConfig(&p4rt));
  ASSIGN_OR_RETURN(IrP4Info info, CreateIrP4Info(config.config().p4info()));
  ASSIGN_OR_RETURN(p4::v1::TableEntry pi_entry,
                   PdTableEntryToPi(info, pd_table_entry));

  // Install entry.
  return InstallPiTableEntry(&p4rt, pi_entry);
}

absl::Status InstallIrTableEntries(P4RuntimeSession& p4rt,
                                   const IrTableEntries& ir_table_entries) {
  // Get P4Info from switch.
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse config,
                   GetForwardingPipelineConfig(&p4rt));
  ASSIGN_OR_RETURN(IrP4Info info, CreateIrP4Info(config.config().p4info()));

  // Convert entries to PI representation.
  ASSIGN_OR_RETURN(std::vector<p4::v1::TableEntry> pi_entries,
                   IrTableEntriesToPi(info, ir_table_entries));

  // Install entries.
  return InstallPiTableEntries(&p4rt, info, pi_entries);
}

absl::Status InstallIrTableEntry(P4RuntimeSession& p4rt,
                                 const IrTableEntry& ir_table_entry) {
  // Get P4Info from switch.
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse config,
                   GetForwardingPipelineConfig(&p4rt));
  ASSIGN_OR_RETURN(IrP4Info info, CreateIrP4Info(config.config().p4info()));

  // Convert entry to PI representation.
  ASSIGN_OR_RETURN(p4::v1::TableEntry pi_entry,
                   IrTableEntryToPi(info, ir_table_entry));

  // Install entry.
  return InstallPiTableEntry(&p4rt, pi_entry);
}

absl::Status InstallPiEntities(P4RuntimeSession& p4rt,
                               const PiEntities& entities) {
  for (const p4::v1::Entity& entity : entities.entities()) {
    RETURN_IF_ERROR(InstallPiEntity(&p4rt, entity));
  }
  return absl::OkStatus();
}

absl::Status InstallPiEntities(P4RuntimeSession& p4rt,
                               absl::string_view entities) {
  ASSIGN_OR_RETURN(auto parsed_entities,
                   gutil::ParseTextProto<PiEntities>(entities));
  return InstallPiEntities(p4rt, parsed_entities);
}

absl::StatusOr<std::vector<p4::v1::TableEntry>> ReadPiTableEntriesSorted(
    P4RuntimeSession& p4rt) {
  ASSIGN_OR_RETURN(std::vector<p4::v1::TableEntry> entries,
                   ReadPiTableEntries(&p4rt));
  // We sort entries based on their key. Since they were read back from the
  // switch, we know that no two entries can have the same key.
  absl::c_sort(entries,
               [](const p4::v1::TableEntry& e1, const p4::v1::TableEntry& e2) {
                 return gutil::TableEntryKey(e1) < gutil::TableEntryKey(e2);
               });

  return entries;
}

absl::StatusOr<IrTableEntries> ReadIrTableEntries(P4RuntimeSession& p4rt) {
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse response,
                   GetForwardingPipelineConfig(&p4rt));
  ASSIGN_OR_RETURN(IrP4Info ir_info,
                   CreateIrP4Info(response.config().p4info()));

  ASSIGN_OR_RETURN(std::vector<p4::v1::TableEntry> entries,
                   ReadPiTableEntries(&p4rt));
  return PiTableEntriesToIr(ir_info, entries);
}

absl::StatusOr<IrTableEntries> ReadIrTableEntriesSorted(
    P4RuntimeSession& p4rt) {
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse response,
                   GetForwardingPipelineConfig(&p4rt));
  ASSIGN_OR_RETURN(IrP4Info ir_info,
                   CreateIrP4Info(response.config().p4info()));

  ASSIGN_OR_RETURN(std::vector<p4::v1::TableEntry> entries,
                   ReadPiTableEntriesSorted(p4rt));
  return PiTableEntriesToIr(ir_info, entries);
}

absl::StatusOr<IrWriteRpcStatus> SendPiUpdatesAndReturnPerUpdateStatus(
    P4RuntimeSession& p4rt, absl::Span<const p4::v1::Update> updates) {
  p4::v1::WriteRequest request;
  request.set_device_id(p4rt.DeviceId());
  request.set_role(p4rt.Role());
  *request.mutable_election_id() = p4rt.ElectionId();

  for (const auto& update : updates) *request.add_updates() = update;

  return GrpcStatusToIrWriteRpcStatus(p4rt.WriteAndReturnGrpcStatus(request),
                                      request.updates_size());
}

absl::StatusOr<IrWriteRpcStatus> SendPiUpdatesAndReturnPerUpdateStatus(
    P4RuntimeSession& p4rt,
    const google::protobuf::RepeatedPtrField<p4::v1::Update>& updates) {
  return SendPiUpdatesAndReturnPerUpdateStatus(
      p4rt, std::vector<p4::v1::Update>(updates.begin(), updates.end()));
}

}  // namespace pdpi

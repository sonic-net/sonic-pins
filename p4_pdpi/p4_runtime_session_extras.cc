#include "p4_pdpi/p4_runtime_session_extras.h"

#include "absl/algorithm/container.h"
#include "gutil/status.h"
#include "gutil/table_entry_key.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/pd.h"

namespace pdpi {
namespace {

// Translates `pi_entries` to IrTableEntries by reading the P4Info used in
// translation from the switch through `p4rt`.
absl::StatusOr<std::vector<IrTableEntry>> TranslatePiEntriesToIrEntries(
    P4RuntimeSession& p4rt, absl::Span<const p4::v1::TableEntry> pi_entries) {
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse response,
                   GetForwardingPipelineConfig(&p4rt));
  ASSIGN_OR_RETURN(IrP4Info ir_info,
                   CreateIrP4Info(response.config().p4info()));

  std::vector<IrTableEntry> ir_table_entries;
  for (const auto& entry : pi_entries) {
    ASSIGN_OR_RETURN(IrTableEntry ir_entry, PiTableEntryToIr(ir_info, entry));
    ir_table_entries.push_back(ir_entry);
  }

  return ir_table_entries;
}

}  // namespace

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

absl::Status InstallIrTableEntries(
    pdpi::P4RuntimeSession& p4rt,
    absl::Span<const pdpi::IrTableEntry> ir_table_entries) {
  // Get P4Info from switch.
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse config,
                   GetForwardingPipelineConfig(&p4rt));
  ASSIGN_OR_RETURN(IrP4Info info, CreateIrP4Info(config.config().p4info()));

  // Convert entries to PI representation.
  std::vector<p4::v1::TableEntry> pi_entries;
  for (const pdpi::IrTableEntry& entry : ir_table_entries) {
    ASSIGN_OR_RETURN(pi_entries.emplace_back(), IrTableEntryToPi(info, entry));
  }

  // Install entries.
  return InstallPiTableEntries(&p4rt, info, pi_entries);
}

absl::Status InstallIrTableEntry(pdpi::P4RuntimeSession& p4rt,
                                 const pdpi::IrTableEntry& ir_table_entry) {
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

absl::StatusOr<std::vector<IrTableEntry>> ReadIrTableEntries(
    P4RuntimeSession& p4rt) {
  ASSIGN_OR_RETURN(std::vector<p4::v1::TableEntry> entries,
                   ReadPiTableEntries(&p4rt));
  return TranslatePiEntriesToIrEntries(p4rt, entries);
}

absl::StatusOr<std::vector<IrTableEntry>> ReadIrTableEntriesSorted(
    P4RuntimeSession& p4rt) {
  ASSIGN_OR_RETURN(std::vector<p4::v1::TableEntry> entries,
                   ReadPiTableEntriesSorted(p4rt));
  return TranslatePiEntriesToIrEntries(p4rt, entries);
}

}  // namespace pdpi

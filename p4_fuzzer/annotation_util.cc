#include "p4_fuzzer/annotation_util.h"

namespace p4_fuzzer {

AnnotatedTableEntry GetAnnotatedTableEntry(
    const pdpi::IrP4Info& ir_p4_info, const p4::v1::TableEntry& entry,
    const std::vector<Mutation> mutations) {
  AnnotatedTableEntry debug_entry;
  *debug_entry.mutable_pi() = entry;

  auto status_or_ir = pdpi::PiTableEntryToIr(ir_p4_info, entry);

  if (!status_or_ir.ok()) {
    debug_entry.set_error(status_or_ir.status().ToString());
  } else {
    *debug_entry.mutable_ir() = status_or_ir.value();
  }

  for (auto mutation : mutations) {
    debug_entry.add_mutations(mutation);
  }

  return debug_entry;
}

AnnotatedUpdate GetAnnotatedUpdate(const pdpi::IrP4Info& ir_p4_info,
                                   const p4::v1::Update& pi_update,
                                   const std::vector<Mutation> mutations) {
  AnnotatedUpdate update;
  *update.mutable_pi() = pi_update;

  auto status_or_ir = pdpi::PiUpdateToIr(ir_p4_info, pi_update);

  if (!status_or_ir.ok()) {
    update.set_error(status_or_ir.status().ToString());
  } else {
    *update.mutable_ir() = status_or_ir.value();
  }

  for (auto mutation : mutations) {
    update.add_mutations(mutation);
  }

  return update;
}

p4::v1::WriteRequest RemoveAnnotations(const AnnotatedWriteRequest& request) {
  p4::v1::WriteRequest base_request;

  base_request.set_device_id(request.device_id());
  *base_request.mutable_election_id() = request.election_id();

  for (const auto& update : request.updates()) {
    *base_request.add_updates() = update.pi();
  }

  return base_request;
}

}  // namespace p4_fuzzer

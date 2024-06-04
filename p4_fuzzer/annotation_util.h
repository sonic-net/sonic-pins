#ifndef P4_FUZZER_ANNOTATION_UTIL_H_
#define P4_FUZZER_ANNOTATION_UTIL_H_

#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/utils/ir.h"

namespace p4_fuzzer {

// Returns an AnnotatedTableEntry.
AnnotatedTableEntry GetAnnotatedTableEntry(
    const pdpi::IrP4Info& ir_p4_info, const p4::v1::TableEntry& entry,
    const std::vector<Mutation> mutations);

// Returns an AnnotatedUpdate.
AnnotatedUpdate GetAnnotatedUpdate(const pdpi::IrP4Info& ir_p4_info,
                                   const p4::v1::Update& pi_update,
                                   const std::vector<Mutation> mutations);

// Creates a P4Runtime WriteRequest from an AnnotatedWriteRequest.
p4::v1::WriteRequest RemoveAnnotations(const AnnotatedWriteRequest& request);

}  // namespace p4_fuzzer

#endif  // P4_FUZZER_ANNOTATION_UTIL_H_

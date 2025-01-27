#ifndef PINS_SAI_P4_INSTANTIATIONS_GOOGLE_SAI_P4INFO_H_
#define PINS_SAI_P4_INSTANTIATIONS_GOOGLE_SAI_P4INFO_H_

#include <vector>

#include "absl/status/statusor.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {

// Returns a reference to a static P4info message for the SAI P4 program for the
// given instantiation. The reference is guaranteed to remain valid at all
// times. If an invalid Instantiation is provided, the method does a LOG(DFATAL)
// and returns an empty P4Info.
const p4::config::v1::P4Info &GetP4Info(Instantiation instantiation);

// TODO: Remove this function in favor of the sai_p4info_builder
// library.
//
// Similar to GetP4Info, but replaces any @sai_hash_seed() annotation with value
// 0 to the provided seed.
// Non-zero seed values are not modified since it is assumed that they have an
// intentionally-defined value in the original P4 file.
p4::config::v1::P4Info GetP4InfoWithHashSeed(Instantiation instantiation,
                                             uint32_t seed);

// Returns a reference to a static IrP4info message for the SAI P4 program.
// The reference is guaranteed to remain valid at all times.  If a invalid
// Instantiation is provided, the method does a LOG(DFATAL) and returns an
// empty IrP4Info.
const pdpi::IrP4Info &GetIrP4Info(Instantiation instantiation);

// Returns a reference to a static unioned P4Info of all instantiations. The
// reference is guaranteed to remain valid at all times. For details of the
// unioning process, see p4info_union_lib.h
const p4::config::v1::P4Info &GetUnionedP4Info();

// Returns a reference to a static unioned IrP4info message for the SAI P4
// program. The reference is guaranteed to remain valid at all times. For
// details of the unioning process, see p4info_union_lib.h
const pdpi::IrP4Info &GetUnionedIrP4Info();

} // namespace sai

#endif // PINS_SAI_P4_INSTANTIATIONS_GOOGLE_SAI_P4INFO_H_

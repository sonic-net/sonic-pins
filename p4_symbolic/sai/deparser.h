#ifndef PINS_P4_SYMBOLIC_SAI_DEPARSER_H_
#define PINS_P4_SYMBOLIC_SAI_DEPARSER_H_

#include "absl/status/statusor.h"
#include "gutil/status.h"
#include "p4_pdpi/string_encodings/bit_string.h"
#include "p4_symbolic/sai/fields.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic {

// Deparses the given packet into a byte string, using values according to the
// given model.
absl::StatusOr<std::string> SaiDeparser(
    const symbolic::SymbolicPerPacketState& packet, const z3::model& model);
absl::StatusOr<std::string> SaiDeparser(const SaiFields& packet,
                                        const z3::model& model);

}  // namespace p4_symbolic
#endif  // PINS_P4_SYMBOLIC_SAI_DEPARSER_H_

#ifndef PINS_P4_PDPI_IR_TOOLS_H_
#define PINS_P4_PDPI_IR_TOOLS_H_

#include <functional>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/variant.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4_pdpi/ir.pb.h"
namespace pdpi {

// `TransformValuesOfType` uses `info` to find all values of `target_type`
// in `entry`, then applies `transformer` to them.
//
// This function fails if:
// * the 'transformer' fails.
// * the `info` and the `entry` are incompatible.
//
// Note that the IR does not include enough information about counters, meters,
// or registers to determine if they use a particular P4NamedType. They are thus
// currently ignored by this function.
absl::Status TransformValuesOfType(
    const IrP4Info& info, const p4::config::v1::P4NamedType& target_type,
    IrTableEntry& entry,
    const std::function<absl::StatusOr<std::string>(absl::string_view)>&
        transformer);

// `TransformValuesOfType` uses `info` to find all values of `target_type`
// in `entries`, then applies `transformer` to them. See the
// `TransformValuesOfType` which acts on a single entry above for further
// information. If this function returns an error, a prefix of the `entries` may
// still be transformed by `transformer`.
absl::Status TransformValuesOfType(
    const IrP4Info& info, const p4::config::v1::P4NamedType& target_type,
    std::vector<IrTableEntry>& entries,
    const std::function<absl::StatusOr<std::string>(absl::string_view)>&
        transformer);

// `VisitValuesOfType` uses `info` to find all values of `target_type`
// in `entries`, then applies `visitor` to them.
// WARNING: This function is inefficient because it copies the entries and uses
// `TransformValuesOfType`, mutating every value of `target_type`.
absl::Status VisitValuesOfType(
    const IrP4Info& info, const p4::config::v1::P4NamedType& target_type,
    std::vector<IrTableEntry> entries,
    const std::function<void(absl::string_view)>& visitor);

}  // namespace pdpi

#endif  // PINS_P4_PDPI_IR_TOOLS_H_

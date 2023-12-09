#ifndef PINS_INFRA_P4_PDPI_HELPERS_H_
#define PINS_INFRA_P4_PDPI_HELPERS_H_

#include <string>

#include "absl/status/statusor.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"

namespace pdpi {

// Returns the table name associated with the given entity.
absl::StatusOr<std::string> EntityToTableName(const IrP4Info& info,
                                              const p4::v1::Entity& entity);
}  // namespace pdpi

#endif  // PINS_INFRA_P4_PDPI_HELPERS_H_

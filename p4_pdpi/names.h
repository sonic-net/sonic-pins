#ifndef PINS_P4_PDPI_NAMES_H_
#define PINS_P4_PDPI_NAMES_H_

#include <string>

#include "absl/status/statusor.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"

namespace pdpi {

// Returns the table name (alias) associated with the given entity.
absl::StatusOr<std::string> EntityToTableName(const IrP4Info &info,
                                              const p4::v1::Entity &entity);

// Returns the table name (alias) associated with the given entity.
absl::StatusOr<std::string> EntityToTableName(const IrEntity &entity);

} // namespace pdpi

#endif // PINS_P4_PDPI_NAMES_H_

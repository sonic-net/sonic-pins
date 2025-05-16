#ifndef PINS_P4_PDPI_IR_PROPERTIES_H_
#define PINS_P4_PDPI_IR_PROPERTIES_H_

#include "p4_pdpi/ir.pb.h"

namespace pdpi {

// Returns true if `match_field` can be absent in a table entry.
bool IsOmittable(const IrMatchFieldDefinition& match_field);

// Returns true if `match_field` has a P4Runtime-translated translated type,as
// expressed through an @p4runtime_translation annotation.
bool HasP4RuntimeTranslatedType(const IrMatchFieldDefinition &match_field);

// Returns true if `param` has a P4Runtime-translated type, as expressed through
// an @p4runtime_translation annotation
bool HasP4RuntimeTranslatedType(
    const IrActionDefinition::IrActionParamDefinition &param);

} // namespace pdpi

#endif // PINS_P4_PDPI_IR_PROPERTIES_H_

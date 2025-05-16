#include "p4_pdpi/ir_properties.h"

#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"

namespace pdpi {

bool IsOmittable(const IrMatchFieldDefinition& match_field) {
  // Note that an unspecified type is not regarded as omittable.
  return match_field.match_field().match_type() ==
             p4::config::v1::MatchField::TERNARY ||
         match_field.match_field().match_type() ==
             p4::config::v1::MatchField::OPTIONAL ||
         match_field.match_field().match_type() ==
             p4::config::v1::MatchField::LPM ||
         match_field.match_field().match_type() ==
             p4::config::v1::MatchField::RANGE;
}

bool HasP4RuntimeTranslatedType(const IrMatchFieldDefinition& match_field) {
  return match_field.match_field().has_type_name() &&
         match_field.format() == pdpi::Format::STRING;
}

bool HasP4RuntimeTranslatedType(
    const IrActionDefinition::IrActionParamDefinition& param) {
  return param.param().has_type_name() &&
         param.format() == pdpi::Format::STRING;
}

}  // namespace pdpi

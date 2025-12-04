// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "p4_infra/p4_pdpi/ir_properties.h"

#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

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

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

#include "gtest/gtest.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pdpi {
namespace {

using ::gutil::ParseProtoOrDie;

TEST(IsOmittable, OmittableTypeReturnsTrue) {
  EXPECT_FALSE(IsOmittable(ParseProtoOrDie<IrMatchFieldDefinition>(
      R"pb(
        match_field { id: 1 name: "required_field" }
      )pb")));

  EXPECT_FALSE(IsOmittable(ParseProtoOrDie<IrMatchFieldDefinition>(
      R"pb(
        match_field { id: 1 name: "required_field" match_type: EXACT }
      )pb")));

  EXPECT_TRUE(IsOmittable(ParseProtoOrDie<IrMatchFieldDefinition>(
      R"pb(
        match_field { id: 1 name: "omittable_field" match_type: OPTIONAL }
      )pb")));

  EXPECT_TRUE(IsOmittable(ParseProtoOrDie<IrMatchFieldDefinition>(
      R"pb(
        match_field { id: 1 name: "omittable_field" match_type: TERNARY }
      )pb")));

  EXPECT_TRUE(IsOmittable(ParseProtoOrDie<IrMatchFieldDefinition>(
      R"pb(
        match_field { id: 1 name: "omittable_field" match_type: LPM }
      )pb")));

  EXPECT_TRUE(IsOmittable(ParseProtoOrDie<IrMatchFieldDefinition>(
      R"pb(
        match_field { id: 1 name: "omittable_field" match_type: RANGE }
      )pb")));
}

TEST(HasP4RuntimeTranslatedType, P4RuntimeTranslatedTypeMatchFieldReturnsTrue) {
  EXPECT_FALSE(
      HasP4RuntimeTranslatedType(ParseProtoOrDie<IrMatchFieldDefinition>(
          R"pb(
            match_field { id: 1 name: "dragon_field" match_type: EXACT }
            format: HEX_STRING
          )pb")));

  EXPECT_FALSE(
      HasP4RuntimeTranslatedType(ParseProtoOrDie<IrMatchFieldDefinition>(
          R"pb(
            match_field {
              id: 1
              name: "dragon_field"
              match_type: EXACT
              type_name { name: "dragon_type" }
            }
            format: HEX_STRING
          )pb")));

  EXPECT_TRUE(
      HasP4RuntimeTranslatedType(ParseProtoOrDie<IrMatchFieldDefinition>(
          R"pb(
            match_field {
              id: 1
              name: "dragon_field"
              match_type: EXACT
              type_name { name: "dragon_type" }
            }
            format: STRING
          )pb")));
}

TEST(HasP4RuntimeTranslatedType, P4RuntimeTranslatedTypeParameterReturnsTrue) {
  EXPECT_FALSE(HasP4RuntimeTranslatedType(
      ParseProtoOrDie<IrActionDefinition::IrActionParamDefinition>(
          R"pb(
            param { id: 1 name: "dragon_param" }
            format: HEX_STRING
          )pb")));

  EXPECT_FALSE(HasP4RuntimeTranslatedType(
      ParseProtoOrDie<IrActionDefinition::IrActionParamDefinition>(
          R"pb(
            param {
              id: 1
              name: "dragon_param"
              type_name { name: "dragon_type" }
            }
            format: HEX_STRING
          )pb")));

  EXPECT_TRUE(HasP4RuntimeTranslatedType(
      ParseProtoOrDie<IrActionDefinition::IrActionParamDefinition>(
          R"pb(
            param {
              id: 1
              name: "dragon_param"
              type_name { name: "dragon_type" }
            }
            format: STRING
          )pb")));
}

}  // namespace
}  // namespace pdpi

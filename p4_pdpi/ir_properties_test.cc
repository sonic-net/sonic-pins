#include "p4_pdpi/ir_properties.h"

#include "gtest/gtest.h"
#include "gutil/testing.h"
#include "p4_pdpi/ir.pb.h"
namespace pdpi {
namespace {

using gutil::ParseProtoOrDie;

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

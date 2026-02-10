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

#include "p4_infra/p4_pdpi/references.h"

#include "absl/hash/hash_testing.h"
#include "gtest/gtest.h"
namespace pdpi {
namespace {

// -- Concrete Reference Field Test --------------------------------------------

TEST(ConcreteFieldReferenceTest, FieldsWithSrcNameDiffAreNotEqual) {
  EXPECT_NE((ConcreteFieldReference{
                .source_field = "Src1",
                .destination_field = "Dst",
                .value = "v",
            }),
            (ConcreteFieldReference{
                .source_field = "Src2",
                .destination_field = "Dst",
                .value = "v",
            }));
}

TEST(ConcreteFieldReferenceTest, FieldsWithDstNameDiffAreNotEqual) {
  EXPECT_NE((ConcreteFieldReference{
                .source_field = "Src",
                .destination_field = "Dst1",
                .value = "v",
            }),
            (ConcreteFieldReference{
                .source_field = "Src",
                .destination_field = "Dst2",
                .value = "v",
            }));
}

TEST(ConcreteFieldReferenceTest, FieldsWithValueDiffAreNotEqual) {
  EXPECT_NE((ConcreteFieldReference{
                .source_field = "Src",
                .destination_field = "Dst",
                .value = "v1",
            }),
            (ConcreteFieldReference{
                .source_field = "Src",
                .destination_field = "Dst",
                .value = "v2",
            }));
}

TEST(ConcreteFieldReferenceTest, IdenticalFieldsAreEqual) {
  EXPECT_EQ((ConcreteFieldReference{
                .source_field = "Src",
                .destination_field = "Dst",
                .value = "v",
            }),
            (ConcreteFieldReference{
                .source_field = "Src",
                .destination_field = "Dst",
                .value = "v",
            }));
}

// The hash value check is provided by VerifyTypeImplementsAbslHashCorrectly
// that checks `ReferenceField`s that are equal have the same hash values and
// `ReferenceField`s that are not equal have different hash values.
TEST(ConcreteFieldReferenceTest, HashingTest) {
  EXPECT_TRUE(absl::VerifyTypeImplementsAbslHashCorrectly({
      (ConcreteFieldReference{
          .source_field = "Src",
          .destination_field = "Dst",
          .value = "v",
      }),
      (ConcreteFieldReference{
          .source_field = "Src1",
          .destination_field = "Dst",
          .value = "v",
      }),
      (ConcreteFieldReference{
          .source_field = "Src",
          .destination_field = "Dst1",
          .value = "v",
      }),
      (ConcreteFieldReference{
          .source_field = "Src",
          .destination_field = "Dst",
          .value = "v1",
      }),
      (ConcreteFieldReference{
          .source_field = "Src",
          .destination_field = "Dst",
          .value = "v",
      }),
  }));
}

// -- Concrete Reference Entry Test --------------------------------------------

TEST(ConcreteTableReferenceTest, EntriesWithSrcNameDiffAreNotEqual) {
  EXPECT_NE((ConcreteTableReference{
                .source_table = "Src1",
                .destination_table = "Dst",
            }),
            (ConcreteTableReference{
                .source_table = "Src2",
                .destination_table = "Dst",
            }));
}

TEST(ConcreteTableReferenceTest, EntriesWithDstNameDiffAreNotEqual) {
  EXPECT_NE((ConcreteTableReference{
                .source_table = "Src",
                .destination_table = "Dst1",
            }),
            (ConcreteTableReference{
                .source_table = "Src",
                .destination_table = "Dst2",
            }));
}

TEST(ConcreteTableReferenceTest, EntriesWithFieldsDiffAreNotEqual) {
  EXPECT_NE((ConcreteTableReference{.source_table = "Src",
                                    .destination_table = "Dst",
                                    .fields =
                                        {
                                            ConcreteFieldReference{
                                                .source_field = "Src1",
                                                .destination_field = "Dst1",
                                                .value = "v1",
                                            },
                                        }}),
            (ConcreteTableReference{.source_table = "Src",
                                    .destination_table = "Dst",
                                    .fields = {
                                        ConcreteFieldReference{
                                            .source_field = "Src2",
                                            .destination_field = "Dst2",
                                            .value = "v2",
                                        },
                                    }}));
}

TEST(ConcreteTableReferenceTest, IdenticalEntriesAreEqual) {
  EXPECT_EQ((ConcreteTableReference{.source_table = "Src",
                                    .destination_table = "Dst",
                                    .fields =
                                        {
                                            ConcreteFieldReference{
                                                .source_field = "Src1",
                                                .destination_field = "Dst1",
                                                .value = "v1",
                                            },
                                        }}),
            (ConcreteTableReference{.source_table = "Src",
                                    .destination_table = "Dst",
                                    .fields = {
                                        ConcreteFieldReference{
                                            .source_field = "Src1",
                                            .destination_field = "Dst1",
                                            .value = "v1",
                                        },
                                    }}));
}

TEST(ConcreteTableReferenceTest, EntriesWithSameFieldsInDiffOrderAreEqual) {
  EXPECT_EQ((ConcreteTableReference{.source_table = "Src",
                                    .destination_table = "Dst",
                                    .fields =
                                        {
                                            ConcreteFieldReference{
                                                .source_field = "Src2",
                                                .destination_field = "Dst2",
                                                .value = "v2",
                                            },
                                            ConcreteFieldReference{
                                                .source_field = "Src1",
                                                .destination_field = "Dst1",
                                                .value = "v1",
                                            },
                                        }}),
            (ConcreteTableReference{.source_table = "Src",
                                    .destination_table = "Dst",
                                    .fields = {
                                        ConcreteFieldReference{
                                            .source_field = "Src1",
                                            .destination_field = "Dst1",
                                            .value = "v1",
                                        },
                                        ConcreteFieldReference{
                                            .source_field = "Src2",
                                            .destination_field = "Dst2",
                                            .value = "v2",
                                        },
                                    }}));
}

TEST(ConcreteTableReferenceTest, EntriesWithSubsetFieldsAreNotEqual) {
  EXPECT_NE((ConcreteTableReference{.source_table = "Src",
                                    .destination_table = "Dst",
                                    .fields =
                                        {
                                            ConcreteFieldReference{
                                                .source_field = "Src1",
                                                .destination_field = "Dst1",
                                                .value = "v1",
                                            },
                                        }}),
            (ConcreteTableReference{.source_table = "Src",
                                    .destination_table = "Dst",
                                    .fields = {
                                        ConcreteFieldReference{
                                            .source_field = "Src1",
                                            .destination_field = "Dst1",
                                            .value = "v1",
                                        },
                                        ConcreteFieldReference{
                                            .source_field = "Src2",
                                            .destination_field = "Dst2",
                                            .value = "v2",
                                        },
                                    }}));
}

// The hash value check is provided by VerifyTypeImplementsAbslHashCorrectly
// that checks `ReferenceField`s that are equal have the same hash values and
// `ReferenceField`s that are not equal have different hash values.
TEST(ConcreteTableReferenceTest, HashingTest) {
  EXPECT_TRUE(absl::VerifyTypeImplementsAbslHashCorrectly(
      {(ConcreteTableReference{.source_table = "Src",
                               .destination_table = "Dst",
                               .fields =
                                   {
                                       ConcreteFieldReference{
                                           .source_field = "Src1",
                                           .destination_field = "Dst1",
                                           .value = "v1",
                                       },
                                   }}),
       (ConcreteTableReference{.source_table = "Src",
                               .destination_table = "Dst",
                               .fields =
                                   {
                                       ConcreteFieldReference{
                                           .source_field = "Src2",
                                           .destination_field = "Dst2",
                                           .value = "v1",
                                       },
                                   }}),
       (ConcreteTableReference{.source_table = "Src",
                               .destination_table = "Dst",
                               .fields =
                                   {
                                       ConcreteFieldReference{
                                           .source_field = "Src1",
                                           .destination_field = "Dst1",
                                           .value = "v1",
                                       },
                                       ConcreteFieldReference{
                                           .source_field = "Src2",
                                           .destination_field = "Dst2",
                                           .value = "v1",
                                       },
                                   }}),
       (ConcreteTableReference{.source_table = "Src",
                               .destination_table = "Dst",
                               .fields =
                                   {
                                       ConcreteFieldReference{
                                           .source_field = "Src2",
                                           .destination_field = "Dst2",
                                           .value = "v1",
                                       },
                                       ConcreteFieldReference{
                                           .source_field = "Src1",
                                           .destination_field = "Dst1",
                                           .value = "v1",
                                       },
                                   }}),
       (ConcreteTableReference{.source_table = "OtherSrc",
                               .destination_table = "Dst",
                               .fields =
                                   {
                                       ConcreteFieldReference{
                                           .source_field = "Src2",
                                           .destination_field = "Dst2",
                                           .value = "v1",
                                       },
                                       ConcreteFieldReference{
                                           .source_field = "Src1",
                                           .destination_field = "Dst1",
                                           .value = "v1",
                                       },
                                   }}),
       (ConcreteTableReference{.source_table = "Src",
                               .destination_table = "OtherDst",
                               .fields = {
                                   ConcreteFieldReference{
                                       .source_field = "Src2",
                                       .destination_field = "Dst2",
                                       .value = "v1",
                                   },
                                   ConcreteFieldReference{
                                       .source_field = "Src1",
                                       .destination_field = "Dst1",
                                       .value = "v1",
                                   },
                               }})}));
}

}  // namespace
}  // namespace pdpi

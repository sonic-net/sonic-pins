// Copyright 2020 Google LLC
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
#include "proto_matchers.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"

namespace gutil {
namespace {

TEST(ProtoMatcher, EqualsProto) {
  pdpi::IrTableEntry table_entry;
  table_entry.set_table_name("router_interface_table");
  table_entry.set_priority(123);

  EXPECT_THAT(table_entry, EqualsProto(table_entry));
}

TEST(ProtoMatcher, EqualsProtoFromText) {
  pdpi::IrTableEntry table_entry;
  table_entry.set_table_name("router_interface_table");
  table_entry.set_priority(123);

  EXPECT_THAT(table_entry, EqualsProto(R"pb(
                table_name: "router_interface_table"
                priority: 123)pb"));
}

}  // namespace
}  // namespace gutil

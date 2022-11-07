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

#include <iostream>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "glog/logging.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/testing/test_helper.h"

using ::gutil::PrintTextProto;
using ::p4::config::v1::P4Info;

static void RunP4InfoTest(const std::string& test_name, const P4Info& p4info) {
  std::cout << TestHeader(test_name) << std::endl << std::endl;
  std::cout << "P4Info input:" << std::endl;
  std::cout << PrintTextProto(p4info) << std::endl;
  absl::StatusOr<pdpi::IrP4Info> status_or_info = pdpi::CreateIrP4Info(p4info);
  std::cout << "pdpi::CreateIrP4Info() result:" << std::endl;
  if (!status_or_info.ok()) {
    std::cout << TestStatusToString(status_or_info.status()) << std::endl;
  } else {
    std::cout << PrintTextProto(status_or_info.value()) << std::endl;
  }
  std::cout << std::endl;
}

int main(int argc, char** argv) {
  // Usage: info_test <p4info file>.
  if (argc != 2) {
    std::cerr << "Invalid number of arguments." << std::endl;
    return 1;
  }
  const auto p4info =
      gutil::ParseProtoFileOrDie<p4::config::v1::P4Info>(argv[1]);

  RunP4InfoTest("missing action definition",
                gutil::ParseProtoOrDie<P4Info>(
                    R"pb(tables {
                           preamble { id: 1 name: "table1" alias: "table1" }
                           action_refs {
                             id: 1  # not defined
                           }
                           size: 1024
                         })pb"));

  RunP4InfoTest("duplicate table id",
                gutil::ParseProtoOrDie<P4Info>(
                    R"pb(tables {
                           preamble { id: 1 name: "table1" alias: "table1" }
                         }
                         tables {
                           preamble { id: 1 name: "table2" alias: "table2" }
                         })pb"));

  RunP4InfoTest("duplicate match field id",
                gutil::ParseProtoOrDie<P4Info>(
                    R"pb(tables {
                           preamble { id: 1 name: "table1" alias: "table1" }
                           match_fields {
                             id: 1
                             name: "field1"
                             bitwidth: 1
                             match_type: EXACT
                           }
                           match_fields {
                             id: 1
                             name: "field2"
                             bitwidth: 1
                             match_type: EXACT
                           }
                         })pb"));

  RunP4InfoTest(
      "duplicate action id",
      gutil::ParseProtoOrDie<P4Info>(
          R"pb(actions {
                 preamble { id: 1 name: "do_thing_1" alias: "do_thing_1" }
               }
               actions {
                 preamble { id: 1 name: "do_thing_2" alias: "do_thing_2" }
               })pb"));

  RunP4InfoTest(
      "duplicate param id",
      gutil::ParseProtoOrDie<P4Info>(
          R"pb(actions {
                 preamble { id: 1 name: "do_thing_1" alias: "do_thing_1" }
                 params { id: 1 name: "param1" }
                 params { id: 1 name: "param2" }
               })pb"));

  RunP4InfoTest("duplicate table name",
                gutil::ParseProtoOrDie<P4Info>(
                    R"pb(tables {
                           preamble { id: 1 name: "table1" alias: "table1" }
                         }
                         tables {
                           preamble { id: 2 name: "table2" alias: "table1" }
                         })pb"));

  RunP4InfoTest("duplicate match field name",
                gutil::ParseProtoOrDie<P4Info>(
                    R"pb(tables {
                           preamble { id: 1 name: "table1" alias: "table1" }
                           match_fields {
                             id: 1
                             name: "field1"
                             bitwidth: 1
                             match_type: EXACT
                           }
                           match_fields {
                             id: 2
                             name: "field1"
                             bitwidth: 1
                             match_type: EXACT
                           }
                         })pb"));

  RunP4InfoTest(
      "duplicate action name",
      gutil::ParseProtoOrDie<P4Info>(
          R"pb(actions {
                 preamble { id: 1 name: "do_thing_1" alias: "do_thing_1" }
               }
               actions {
                 preamble { id: 2 name: "do_thing_2" alias: "do_thing_1" }
               })pb"));

  RunP4InfoTest("duplicate param name", gutil::ParseProtoOrDie<P4Info>(R"pb(
                  actions {
                    preamble { id: 1 name: "do_thing_1" alias: "do_thing_1" }
                    params { id: 1 name: "param1" }
                    params { id: 2 name: "param1" }
                  })pb"));

  RunP4InfoTest(
      "invalid format annotation", gutil::ParseProtoOrDie<P4Info>(R"pb(
        actions {
          preamble { id: 1 name: "do_thing_1" alias: "do_thing_1" }
          params { id: 1 name: "param1" }
          params { id: 2 name: "param2" annotations: "@format(IPVx_ADDRESS)" }
        })pb"));

  RunP4InfoTest("main.p4", p4info);

  return 0;
}

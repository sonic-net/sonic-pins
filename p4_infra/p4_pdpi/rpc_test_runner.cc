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
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "google/protobuf/any.pb.h"
#include "google/protobuf/util/message_differencer.h"
#include "google/rpc/code.pb.h"
#include "google/rpc/status.pb.h"
#include "grpcpp/grpcpp.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/main_p4_pd.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_pdpi/test_helper.h"
#include "p4_infra/p4_pdpi/translation_options.h"

using ::gutil::PrintTextProto;
using ::p4::config::v1::P4Info;

// Overload the StatusOr insertion operator to output its status. This allows
// StatusOr to be directly used in LOG messages.
template <typename T>
std::ostream& operator<<(std::ostream& out,
                         const absl::StatusOr<T>& status_or) {
  return out << status_or.status();
}

static void RunPiReadRequestTest(const pdpi::IrP4Info& info,
                                 const std::string& test_name,
                                 const p4::v1::ReadRequest& pi,
                                 pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPiTest<pdpi::IrReadRequest, p4::v1::ReadRequest>(
      info, absl::StrCat("ReadRequest test: ", test_name), pi, options,
      pdpi::PiReadRequestToIr);
}

static void RunPdReadRequestTest(const pdpi::IrP4Info& info,
                                 const std::string& test_name,
                                 const pdpi::ReadRequest& pd,
                                 const pdpi::InputValidity validity,
                                 pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPdTest<pdpi::ReadRequest, pdpi::IrReadRequest,
                         p4::v1::ReadRequest>(
      info, absl::StrCat("ReadRequest test: ", test_name), pd, options,
      pdpi::PdReadRequestToIr, pdpi::IrReadRequestToPd, pdpi::IrReadRequestToPi,
      pdpi::PiReadRequestToIr, pdpi::PdReadRequestToPi, pdpi::PiReadRequestToPd,
      validity);
}

static void RunPiReadResponseTest(const pdpi::IrP4Info& info,
                                  const std::string& test_name,
                                  const p4::v1::ReadResponse& pi,
                                  pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPiTest<pdpi::IrReadResponse, p4::v1::ReadResponse>(
      info, absl::StrCat("ReadResponse test: ", test_name), pi, options,
      // We cannot pass `PiReadResponseToIr` directly, since it takes an
      // optional third parameter, which `RunGenericPiTest` does not expect.
      [](const pdpi::IrP4Info& info, const p4::v1::ReadResponse& pi,
         pdpi::TranslationOptions options) {
        return pdpi::PiReadResponseToIr(info, pi);
      });
}

static void RunPdReadResponseTest(const pdpi::IrP4Info& info,
                                  const std::string& test_name,
                                  const pdpi::ReadResponse& pd,
                                  const pdpi::InputValidity validity,
                                  pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPdTest<pdpi::ReadResponse, pdpi::IrReadResponse,
                         p4::v1::ReadResponse>(
      info, absl::StrCat("ReadResponse test: ", test_name), pd, options,
      pdpi::PdReadResponseToIr, pdpi::IrReadResponseToPd,
      pdpi::IrReadResponseToPi, pdpi::PiReadResponseToIr,
      pdpi::PdReadResponseToPi, pdpi::PiReadResponseToPd, validity);
}

static void RunPiUpdateTest(const pdpi::IrP4Info& info,
                            const std::string& test_name,
                            const p4::v1::Update& pi,
                            pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPiTest<pdpi::IrUpdate, p4::v1::Update>(
      info, absl::StrCat("Update test: ", test_name), pi, options,
      // We cannot pass `PiUpdateToIr` directly, since it takes an optional
      // third parameter, which `RunGenericPiTest` does not expect.
      [](const pdpi::IrP4Info& info, const p4::v1::Update& pi,
         pdpi::TranslationOptions options) {
        return pdpi::PiUpdateToIr(info, pi);
      });
}

static void RunPdUpdateTest(const pdpi::IrP4Info& info,
                            const std::string& test_name,
                            const pdpi::Update& pd,
                            const pdpi::InputValidity validity,
                            pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPdTest<pdpi::Update, pdpi::IrUpdate, p4::v1::Update>(
      info, absl::StrCat("Update test: ", test_name), pd, options,
      pdpi::PdUpdateToIr, pdpi::IrUpdateToPd, pdpi::IrUpdateToPi,
      pdpi::PiUpdateToIr, pdpi::PdUpdateToPi, pdpi::PiUpdateToPd, validity);
}

static void RunPiWriteRequestTest(const pdpi::IrP4Info& info,
                                  const std::string& test_name,
                                  const p4::v1::WriteRequest& pi,
                                  pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPiTest<pdpi::IrWriteRequest, p4::v1::WriteRequest>(
      info, absl::StrCat("WriteRequest test: ", test_name), pi, options,
      // We cannot pass `PiWriteRequestToIr` directly, since it takes an
      // optional third parameter, which `RunGenericPiTest` does not expect.
      [](const pdpi::IrP4Info& info, const p4::v1::WriteRequest& pi,
         pdpi::TranslationOptions options) {
        return pdpi::PiWriteRequestToIr(info, pi);
      });
}

static void RunPdWriteRequestTest(const pdpi::IrP4Info& info,
                                  const std::string& test_name,
                                  const pdpi::WriteRequest& pd,
                                  const pdpi::InputValidity validity,
                                  pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPdTest<pdpi::WriteRequest, pdpi::IrWriteRequest,
                         p4::v1::WriteRequest>(
      info, absl::StrCat("WriteRequest test: ", test_name), pd, options,
      pdpi::PdWriteRequestToIr, pdpi::IrWriteRequestToPd,
      pdpi::IrWriteRequestToPi, pdpi::PiWriteRequestToIr,
      pdpi::PdWriteRequestToPi, pdpi::PiWriteRequestToPd, validity);
}

static void RunInvalidGrpcFailToTranslateToIrTest(
    const std::string& test_name, int number_of_write_request,
    const grpc::Status& grpc_status) {
  std::cout << pdpi::TestHeader(absl::StrCat(
                   "Invalid gRPC WriteRpcStatus should fail test: ", test_name))
            << std::endl
            << std::endl;
  std::cout << "--- gRPC (Input):" << std::endl;
  std::cout << pdpi::WriteRequestGrpcStatusToString(grpc_status);

  // Grpc -> Absl
  std::cout << "--- absl::Status:" << std::endl;
  std::cout << pdpi::TestStatusToString(pdpi::WriteRpcGrpcStatusToAbslStatus(
                   grpc_status, number_of_write_request))
            << std::endl;

  // Grpc -> IR
  const auto& status_or_ir =
      pdpi::GrpcStatusToIrWriteRpcStatus(grpc_status, number_of_write_request);
  if (!status_or_ir.ok()) {
    std::cout << "--- gRPC is invalid/unsupported:" << std::endl;
    std::cout << pdpi::TestStatusToString(status_or_ir.status()) << std::endl
              << std::endl;
  } else {
    pdpi::Fail(test_name, "Expected gRPC status to be invalid.");
  }
}

static void RunInvalidIrFailToTranslateToGrpcTest(
    const std::string& test_name,
    const pdpi::IrWriteRpcStatus& ir_write_rpc_status) {
  std::cout << pdpi::TestHeader(absl::StrCat(
                   "Invalid Ir WriteRpcStatus should fail test: ", test_name))
            << std::endl
            << std::endl;
  std::cout << "--- IR (Input):" << std::endl;
  std::cout << PrintTextProto(ir_write_rpc_status);
  const auto& status_or_grpc =
      pdpi::IrWriteRpcStatusToGrpcStatus(ir_write_rpc_status);
  if (!status_or_grpc.ok()) {
    std::cout << "--- IR is invalid/unsupported:" << std::endl
              << pdpi::TestStatusToString(status_or_grpc.status()) << std::endl
              << std::endl;
  } else {
    pdpi::Fail(test_name, "Expected IR to be invalid.");
  }
}

// Runs PD -> IR -> Grpc -> IR2 -> PD2 and if validity == INPUT_IS_VALID, checks
// IR == IR2 and  PD == PD2
static void RunPdWriteRpcStatusTest(const std::string& test_name,
                                    const pdpi::WriteRpcStatus& pd,
                                    int number_of_update_status,
                                    pdpi::InputValidity validity,
                                    pdpi::TranslationOptions options = {}) {
  if (validity == pdpi::INPUT_IS_VALID) {
    std::cout << pdpi::TestHeader(
        absl::StrCat("Pd WriteRpcStatus test (INPUT_IS_VALID): ", test_name));
  } else {
    std::cout << pdpi::TestHeader(
        absl::StrCat("Pd WriteRpcStatus test (INPUT_IS_INVALID): ", test_name));
  }
  std::cout << std::endl << std::endl;
  std::cout << "--- PD(input):" << std::endl;
  std::cout << PrintTextProto(pd) << std::endl;
  // Set-up message differencer.
  google::protobuf::util::MessageDifferencer diff;
  diff.set_report_moves(false);
  diff.set_repeated_field_comparison(
      google::protobuf::util::MessageDifferencer::RepeatedFieldComparison::
          AS_SET);
  std::string explanation;
  diff.ReportDifferencesToString(&explanation);

  // PD -> IR
  const auto& status_or_ir = pdpi::PdWriteRpcStatusToIr(pd, options);
  if (!status_or_ir.ok()) {
    if (validity == pdpi::INPUT_IS_VALID) {
      pdpi::Fail(
          test_name,
          "Translation from PD to IR failed even though input was marked "
          "valid.");
      std::cout << status_or_ir.status().message() << std::endl;
      return;
    } else {
      std::cout << "---PD is invalid/unsupported:" << std::endl;
      std::cout << pdpi::TestStatusToString(status_or_ir.status()) << std::endl
                << std::endl
                << std::endl;
      return;
    }
  }
  const auto& ir = status_or_ir.value();
  std::cout << "---IR:" << std::endl;
  std::cout << PrintTextProto(ir) << std::endl;

  // IR -> Grpc
  const auto& status_or_grpc_status = pdpi::IrWriteRpcStatusToGrpcStatus(ir);
  if (!status_or_grpc_status.ok()) {
    if (validity == pdpi::INPUT_IS_VALID) {
      pdpi::Fail(
          test_name,
          "Translation from IR to gRPC failed even though input was marked "
          "valid.");
      std::cout << status_or_grpc_status.status().message() << std::endl;
      return;
    } else {
      std::cout << "---PD is invalid/unsupported (detected when translating IR "
                   "to gRPC.)\n";
      std::cout << status_or_grpc_status.status().message() << std::endl
                << std::endl
                << std::endl;
      return;
    }
  }
  if (validity == pdpi::INPUT_IS_INVALID) {
    pdpi::Fail(
        test_name,
        "PD was marked invalid but translation from PD to IR and IR to gRPC "
        "both succeeded.");
    return;
  }

  // At this point, validity == INPUT_IS_VALID
  const auto& grpc_write_status = status_or_grpc_status.value();
  std::cout << "---gRPC Status:" << std::endl;
  std::cout << pdpi::WriteRequestGrpcStatusToString(grpc_write_status)
            << std::endl;

  // Grpc -> Absl
  std::cout << "--- absl::Status:" << std::endl;
  std::cout << pdpi::TestStatusToString(pdpi::WriteRpcGrpcStatusToAbslStatus(
                   grpc_write_status, number_of_update_status))
            << std::endl;

  // Grpc -> IR2
  const auto& status_or_ir2 = pdpi::GrpcStatusToIrWriteRpcStatus(
      grpc_write_status, number_of_update_status);
  if (!status_or_ir2.ok()) {
    pdpi::Fail(test_name, "Translation from gRPC to IR failed");
    std::cout << status_or_ir2.status().message() << std::endl;
    return;
  }
  const auto& ir2 = status_or_ir2.value();
  if (!diff.Compare(ir, ir2)) {
    pdpi::Fail(
        test_name,
        "Reverse translation from gRPC to IR resulted in a different IR.");
    std::cout << "Differences: " << explanation << std::endl;
    std::cout << "IR(after reverse translation):" << std::endl
              << PrintTextProto(ir2) << std::endl;
    return;
  }

  // IR2 -> PD2
  pdpi::WriteRpcStatus pd2;
  const auto pd2_translation_status = pdpi::IrWriteRpcStatusToPd(ir, &pd2);

  if (!pd2_translation_status.ok()) {
    pdpi::Fail(test_name, "Translation from IR2 to PD2 failed");
    std::cout << pd2_translation_status.message() << std::endl;
    return;
  }
  if (!diff.Compare(pd, pd2)) {
    pdpi::Fail(
        test_name,
        "Reverse translation from IR2 to PD2 resulted in a different PD");
    std::cout << "Differences: " << explanation << std::endl;
    std::cout << "PD(after reverse translation):" << std::endl
              << PrintTextProto(pd2) << std::endl;
    return;
  }
  std::cout << std::endl;
}

static void RunPiStreamMessageRequestTest(
    const pdpi::IrP4Info& info, const std::string& test_name,
    const p4::v1::StreamMessageRequest& pi,
    pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPiTest<pdpi::IrStreamMessageRequest,
                         p4::v1::StreamMessageRequest>(
      info, absl::StrCat("StreamMessageRequest test: ", test_name), pi, options,
      pdpi::PiStreamMessageRequestToIr);
}

static void RunPdStreamMessageRequestTest(
    const pdpi::IrP4Info& info, const std::string& test_name,
    const pdpi::StreamMessageRequest& pd, const pdpi::InputValidity validity,
    pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPdTest<pdpi::StreamMessageRequest,
                         pdpi::IrStreamMessageRequest,
                         p4::v1::StreamMessageRequest>(
      info, absl::StrCat("StreamMessageRequest test: ", test_name), pd, options,
      pdpi::PdStreamMessageRequestToIr, pdpi::IrStreamMessageRequestToPd,
      pdpi::IrStreamMessageRequestToPi, pdpi::PiStreamMessageRequestToIr,
      pdpi::PdStreamMessageRequestToPi, pdpi::PiStreamMessageRequestToPd,
      validity);
}

static void RunPiStreamMessageResponseTest(
    const pdpi::IrP4Info& info, const std::string& test_name,
    const p4::v1::StreamMessageResponse& pi,
    pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPiTest<pdpi::IrStreamMessageResponse,
                         p4::v1::StreamMessageResponse>(
      info, absl::StrCat("StreamMessageResponse test: ", test_name), pi,
      options, pdpi::PiStreamMessageResponseToIr);
}

static void RunPdStreamMessageResponseTest(
    const pdpi::IrP4Info& info, const std::string& test_name,
    const pdpi::StreamMessageResponse& pd, const pdpi::InputValidity validity,
    pdpi::TranslationOptions options = {}) {
  pdpi::RunGenericPdTest<pdpi::StreamMessageResponse,
                         pdpi::IrStreamMessageResponse,
                         p4::v1::StreamMessageResponse>(
      info, absl::StrCat("StreamMessageResponse test: ", test_name), pd,
      options, pdpi::PdStreamMessageResponseToIr,
      pdpi::IrStreamMessageResponseToPd, pdpi::IrStreamMessageResponseToPi,
      pdpi::PiStreamMessageResponseToIr, pdpi::PdStreamMessageResponseToPi,
      pdpi::PiStreamMessageResponseToPd, validity);
}

static void RunReadRequestTests(const pdpi::IrP4Info& info) {
  RunPiReadRequestTest(info, "empty",
                       gutil::ParseProtoOrDie<p4::v1::ReadRequest>(""));

  RunPiReadRequestTest(info, "no entities",
                       gutil::ParseProtoOrDie<p4::v1::ReadRequest>(R"pb(
                         device_id: 10
                       )pb"));

  RunPiReadRequestTest(info, "wrong entities",
                       gutil::ParseProtoOrDie<p4::v1::ReadRequest>(R"pb(
                         device_id: 10
                         entities { action_profile_member {} }
                       )pb"));

  RunPiReadRequestTest(info, "multiple table entries",
                       gutil::ParseProtoOrDie<p4::v1::ReadRequest>(R"pb(
                         device_id: 10
                         entities { table_entry {} }
                         entities { table_entry {} }
                       )pb"));

  // There are no invalid IR read requests, so no RunIrReadRequestTest is
  // needed.

  RunPdReadRequestTest(info, "no meter, no counter",
                       gutil::ParseProtoOrDie<pdpi::ReadRequest>(R"pb(
                         device_id: 10
                       )pb"),
                       pdpi::INPUT_IS_VALID);
  RunPdReadRequestTest(info, "meter, no counter",
                       gutil::ParseProtoOrDie<pdpi::ReadRequest>(R"pb(
                         device_id: 10
                         read_meter_configs: true
                       )pb"),
                       pdpi::INPUT_IS_VALID);
  RunPdReadRequestTest(info, "no meter, counter",
                       gutil::ParseProtoOrDie<pdpi::ReadRequest>(R"pb(
                         device_id: 10
                         read_counter_data: true
                       )pb"),
                       pdpi::INPUT_IS_VALID);
  RunPdReadRequestTest(info, "meter, counter",
                       gutil::ParseProtoOrDie<pdpi::ReadRequest>(R"pb(
                         device_id: 10
                         read_meter_configs: true
                         read_counter_data: true
                       )pb"),
                       pdpi::INPUT_IS_VALID);
}

static void RunReadResponseTests(const pdpi::IrP4Info& info) {
  RunPiReadResponseTest(info, "wrong entity",
                        gutil::ParseProtoOrDie<p4::v1::ReadResponse>(R"pb(
                          entities { action_profile_member {} }
                        )pb"));

  // Invalid IR read responses are tested in table_entry_test.cc, so no
  // RunIrReadResponseTest is needed.

  RunPdReadResponseTest(
      info, "valid ternary table",
      gutil::ParseProtoOrDie<pdpi::ReadResponse>(R"pb(
        table_entries {
          ternary_table_entry {
            match { normal { value: "0x052" mask: "0x273" } }
            priority: 32
            action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
          }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);
  RunPdReadResponseTest(
      info, "valid multicast group table",
      gutil::ParseProtoOrDie<pdpi::ReadResponse>(R"pb(
        table_entries {
          multicast_group_table_entry {
            match { multicast_group_id: "0x0001" }
            action { replicate { replicas { port: "1" instance: "0x0001" } } }
          }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);

  RunPdReadResponseTest(
      info, "multiple tables", gutil::ParseProtoOrDie<pdpi::ReadResponse>(R"pb(
        table_entries {
          ternary_table_entry {
            match { normal { value: "0x052" mask: "0x273" } }
            priority: 32
            action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
          }
        }
        table_entries {
          ternary_table_entry {
            match { normal { value: "0x052" mask: "0x273" } }
            priority: 32
            action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
          }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);
}

static void RunUpdateTests(pdpi::IrP4Info info) {
  RunPiUpdateTest(info, "empty", gutil::ParseProtoOrDie<p4::v1::Update>(R"pb(
                  )pb"));

  RunPiUpdateTest(info, "missing type",
                  gutil::ParseProtoOrDie<p4::v1::Update>(R"pb(
                    entity { table_entry {} }
                  )pb"));

  RunPiUpdateTest(info, "wrong entity",
                  gutil::ParseProtoOrDie<p4::v1::Update>(R"pb(
                    type: INSERT
                    entity { action_profile_member {} }
                  )pb"));

  // Invalid IR update table_entries are tested in table_entry_test.cc and
  // invalid type is tested in PD tests. No RunIrUpdateTest is needed.

  RunPdUpdateTest(
      info, "missing type", gutil::ParseProtoOrDie<pdpi::Update>(R"pb(
        table_entry {
          ternary_table_entry {
            match { normal { value: "0x052" mask: "0x273" } }
            priority: 32
            action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
          }
        }
      )pb"),
      pdpi::INPUT_IS_INVALID);

  RunPdUpdateTest(
      info, "valid ternary table", gutil::ParseProtoOrDie<pdpi::Update>(R"pb(
        type: MODIFY
        table_entry {
          ternary_table_entry {
            match { normal { value: "0x052" mask: "0x273" } }
            priority: 32
            action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
          }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);
  RunPdUpdateTest(
      info, "valid mulitcast group table",
      gutil::ParseProtoOrDie<pdpi::Update>(R"pb(
        type: INSERT
        table_entry {
          multicast_group_table_entry {
            match { multicast_group_id: "0x0001" }
            action { replicate { replicas { port: "1" instance: "0x0001" } } }
          }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);
}

static void RunWriteRequestTests(pdpi::IrP4Info info) {
  RunPiWriteRequestTest(info, "invalid role_id",
                        gutil::ParseProtoOrDie<p4::v1::WriteRequest>(R"pb(
                          role_id: 1
                        )pb"));

  RunPiWriteRequestTest(info, "invalid atomicity",
                        gutil::ParseProtoOrDie<p4::v1::WriteRequest>(R"pb(
                          role_id: 0
                          atomicity: ROLLBACK_ON_ERROR
                        )pb"));

  // Invalid updates values are tested in RunUpdateTests.
  // Invalid IR WriteRequests are tested in PD tests. No RunIrWriteRequestTest
  // is needed.

  RunPdWriteRequestTest(info, "empty",
                        gutil::ParseProtoOrDie<pdpi::WriteRequest>(R"pb(
                        )pb"),
                        pdpi::INPUT_IS_VALID);

  RunPdWriteRequestTest(info, "missing updates",
                        gutil::ParseProtoOrDie<pdpi::WriteRequest>(R"pb(
                          device_id: 134
                          election_id { high: 23413 low: 2312 }
                        )pb"),
                        pdpi::INPUT_IS_VALID);

  RunPdWriteRequestTest(
      info, "valid ternary table update",
      gutil::ParseProtoOrDie<pdpi::WriteRequest>(R"pb(
        device_id: 113
        election_id { high: 1231 low: 77989 }
        updates {
          type: MODIFY
          table_entry {
            ternary_table_entry {
              match { normal { value: "0x052" mask: "0x273" } }
              priority: 32
              action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
            }
          }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);
  RunPdWriteRequestTest(
      info, "valid multicast group table update",
      gutil::ParseProtoOrDie<pdpi::WriteRequest>(R"pb(
        device_id: 113
        election_id { high: 1231 low: 77989 }
        updates {
          type: INSERT
          table_entry {
            multicast_group_table_entry {
              match { multicast_group_id: "0x0001" }
              action { replicate { replicas { port: "1" instance: "0x0001" } } }
            }
          }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);
  RunPdWriteRequestTest(
      info, "multiple updates", gutil::ParseProtoOrDie<pdpi::WriteRequest>(R"pb(
        device_id: 113
        election_id { high: 1231 low: 77989 }
        updates {
          type: MODIFY
          table_entry {
            ternary_table_entry {
              match { normal { value: "0x052" mask: "0x273" } }
              priority: 32
              action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
            }
          }
        }
        updates {
          type: DELETE
          table_entry {
            ternary_table_entry {
              match { normal { value: "0x052" mask: "0x273" } }
              priority: 32
              action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
            }
          }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);
  RunPdWriteRequestTest(
      info, "multiple updates, some invalid",
      gutil::ParseProtoOrDie<pdpi::WriteRequest>(R"pb(
        device_id: 113
        election_id { high: 1231 low: 77989 }
        updates {
          type: MODIFY
          table_entry {
            ternary_table_entry {
              match { normal { value: "0x052" mask: "0x273" } }
              priority: 32
              action { do_thing_3 { arg1: "0x01234567" arg2: "0x01234568" } }
            }
          }
        }
        updates {
          type: DELETE
          table_entry {
            ternary_table_entry {
              match { normal { value: "0x052" mask: "0x273" } }
              priority: 32
              action { do_thing_3 { arg2: "0x01234568" } }
            }
          }
        }
      )pb"),
      pdpi::INPUT_IS_INVALID);
}

static google::rpc::Status GenerateGoogleRpcStatus(
    google::rpc::Code status_code, const std::string& message,
    const std::vector<p4::v1::Error>& p4_errors) {
  google::rpc::Status google_rpc_status;
  google_rpc_status.set_code(status_code);
  google_rpc_status.set_message(message);
  for (const auto& p4_error : p4_errors) {
    google_rpc_status.add_details()->PackFrom(p4_error);
  }
  return google_rpc_status;
}

static void RunWriteRpcStatusTest() {
  int number_of_statuses_for_invalid_test = 42;
  RunInvalidGrpcFailToTranslateToIrTest(
      "Grpc status has ok status with non empty message",
      number_of_statuses_for_invalid_test,
      grpc::Status(grpc::StatusCode::OK, "message_string"));
  RunInvalidGrpcFailToTranslateToIrTest(
      "Invalid gRPC StatusCode", number_of_statuses_for_invalid_test,
      grpc::Status(static_cast<grpc::StatusCode>(42), "error_message"));

  // Use p4 errors below to construct google::rpc::status
  p4::v1::Error ok_p4_error =
      gutil::ParseProtoOrDie<p4::v1::Error>(R"pb(canonical_code: 0)pb");
  p4::v1::Error resource_exhausted_p4_error =
      gutil::ParseProtoOrDie<p4::v1::Error>(R"pb(canonical_code: 8
                                                 message: "table is full")pb");
  p4::v1::Error ok_p4_error_message_with_message =
      gutil::ParseProtoOrDie<p4::v1::Error>(R"pb(canonical_code: 0
                                                 message: "some message")pb");
  p4::v1::Error non_ok_p4_error_with_no_message =
      gutil::ParseProtoOrDie<p4::v1::Error>(R"pb(canonical_code: 2)pb");
  p4::v1::Error p4_error_with_invalid_canonical_code =
      gutil::ParseProtoOrDie<p4::v1::Error>(R"pb(canonical_code: 42)pb");

  std::vector<p4::v1::Error> all_ok_p4_errors{ok_p4_error, ok_p4_error,
                                              ok_p4_error};
  grpc::Status all_ok_p4_status_grpc_status(
      grpc::StatusCode::UNKNOWN, "batch update all successful",
      GenerateGoogleRpcStatus(google::rpc::Code::UNKNOWN,
                              "batch update all successful", all_ok_p4_errors)
          .SerializeAsString());
  RunInvalidGrpcFailToTranslateToIrTest(
      "None of p4_error contained in google::rpc::status within grpc::Status "
      "is non-ok",
      all_ok_p4_errors.size(), all_ok_p4_status_grpc_status);

  std::vector<p4::v1::Error> invalid_p4_errors{
      ok_p4_error, resource_exhausted_p4_error,
      ok_p4_error_message_with_message};
  grpc::Status mix_of_success_and_failure_invalid_batch_update_grpc_status(
      grpc::StatusCode::UNKNOWN, "mix of successful and failed batch update",
      GenerateGoogleRpcStatus(google::rpc::Code::UNKNOWN,
                              "mix of successful and failed batch update",
                              invalid_p4_errors)
          .SerializeAsString());
  RunInvalidGrpcFailToTranslateToIrTest(
      "Invalid p4 error has ok status but has non-empty message",
      invalid_p4_errors.size(),
      mix_of_success_and_failure_invalid_batch_update_grpc_status);

  grpc::Status grpc_status_with_inner_status_with_different_message(
      grpc::StatusCode::UNKNOWN, "some message",
      GenerateGoogleRpcStatus(google::rpc::Code::UNKNOWN, "different message",
                              {resource_exhausted_p4_error})
          .SerializeAsString());

  grpc::Status grpc_status_with_inner_status_with_different_code(
      grpc::StatusCode::UNKNOWN, "some message",
      GenerateGoogleRpcStatus(google::rpc::Code::RESOURCE_EXHAUSTED,
                              "some message", {resource_exhausted_p4_error})
          .SerializeAsString());
  RunInvalidGrpcFailToTranslateToIrTest(
      "gRPC status has code that is different from code contained in "
      "google::rpc::Status",
      1, grpc_status_with_inner_status_with_different_code);

  grpc::Status grpc_status_with_mismatching_status_for_batch_update(
      grpc::StatusCode::RESOURCE_EXHAUSTED, "some message",
      GenerateGoogleRpcStatus(google::rpc::Code::RESOURCE_EXHAUSTED,
                              "some message", {resource_exhausted_p4_error})
          .SerializeAsString());
  RunInvalidGrpcFailToTranslateToIrTest(
      "gRPC status contains batch update information but does not have UNKNOWN "
      "status",
      1, grpc_status_with_mismatching_status_for_batch_update);

  grpc::Status grpc_status_with_invalid_p4_error(
      grpc::StatusCode::UNKNOWN, "some message",
      GenerateGoogleRpcStatus(google::rpc::Code::UNKNOWN, "some message",
                              {p4_error_with_invalid_canonical_code})
          .SerializeAsString());
  RunInvalidGrpcFailToTranslateToIrTest(
      "gRPC status has batch update information but p4 error's canonical_code "
      "is not valid",
      1, grpc_status_with_invalid_p4_error);

  RunInvalidIrFailToTranslateToGrpcTest(
      "IR rpc_response has ok code but non empty message",
      gutil::ParseProtoOrDie<pdpi::IrWriteRpcStatus>(R"pb(
        rpc_response: {
          statuses: { code: OK }
          statuses: { code: OK }
          statuses: { code: OK }
          statuses: { code: OK message: "error_message" }
          statuses: { code: OK message: "error_message" }
        }
      )pb"));
  RunInvalidIrFailToTranslateToGrpcTest(
      "IR rpc_response has status with invalid code",
      gutil::ParseProtoOrDie<pdpi::IrWriteRpcStatus>(R"pb(
        rpc_response: {
          statuses: { code: OK }
          statuses: { code: OK }
          statuses: { code: OK }
          statuses: { code: OK }
          statuses: { code: 42 message: "42 is invalid" }
        }
      )pb"));
  RunInvalidIrFailToTranslateToGrpcTest(
      "IR rpc_wide_error has invalid code",
      gutil::ParseProtoOrDie<pdpi::IrWriteRpcStatus>(R"pb(
        rpc_wide_error: { code: 42 message: "invalid_code" }
      )pb"));
  RunInvalidIrFailToTranslateToGrpcTest(
      "IR rpc_wide_error should not have ok status",
      gutil::ParseProtoOrDie<pdpi::IrWriteRpcStatus>(R"pb(
        rpc_wide_error: { code: 0 message: "ok_code" }
      )pb"));

  RunPdWriteRpcStatusTest("PD rpc_wide error has invalid code",
                          gutil::ParseProtoOrDie<pdpi::WriteRpcStatus>(R"pb(
                            rpc_wide_error: { code: 42 message: "bad_code" }
                          )pb"),
                          5, pdpi::INPUT_IS_INVALID);
  RunPdWriteRpcStatusTest("non-ok status with empty message should fail",
                          gutil::ParseProtoOrDie<pdpi::WriteRpcStatus>(R"pb(
                            rpc_response: {
                              statuses: { code: OK }
                              statuses: { code: OK }
                              statuses: { code: OK }
                              statuses: { code: OK message: "error_message" }
                              statuses: { code: OK message: "error_message" }
                            }
                          )pb"),
                          5, pdpi::INPUT_IS_INVALID);
  RunPdWriteRpcStatusTest("invalid status in rpc response",
                          gutil::ParseProtoOrDie<pdpi::WriteRpcStatus>(R"pb(
                            rpc_response: {
                              statuses: { code: 42 }
                              statuses: { code: OK }
                              statuses: { code: OK }
                              statuses: { code: OK }
                              statuses: { code: UNKNOWN }
                            }
                          )pb"),
                          5, pdpi::INPUT_IS_INVALID);

  // Tests translation of PD with all ok status should success when
  // number_of_update_status matches with the repeated statuses field in PD
  RunPdWriteRpcStatusTest("all reads status ok",
                          gutil::ParseProtoOrDie<pdpi::WriteRpcStatus>(R"pb(
                            rpc_response: {
                              statuses: { code: OK }
                              statuses: { code: OK }
                              statuses: { code: OK }
                              statuses: { code: OK }
                              statuses: { code: OK }
                            }
                          )pb"),
                          5, pdpi::INPUT_IS_VALID);
  // RPC-wide error tests
  RunPdWriteRpcStatusTest("rpc-wide error with ok status code",
                          gutil::ParseProtoOrDie<pdpi::WriteRpcStatus>(R"pb(
                            rpc_wide_error: { code: 0 message: "code is ok" }
                          )pb"),
                          5, pdpi::INPUT_IS_INVALID);
  RunPdWriteRpcStatusTest("rpc-wide error with invalid status code",
                          gutil::ParseProtoOrDie<pdpi::WriteRpcStatus>(R"pb(
                            rpc_wide_error: { code: 42 message: "bad_code" }
                          )pb"),
                          5, pdpi::INPUT_IS_INVALID);
  RunPdWriteRpcStatusTest(
      "rpc-wide error with ABORTED status",
      gutil::ParseProtoOrDie<pdpi::WriteRpcStatus>(R"pb(
        rpc_wide_error: { code: 10 message: "int value of ABORTED is 10" }
      )pb"),
      5, pdpi::INPUT_IS_VALID);

  // Mix of successful and failed batch write update.
  // This is the same error status in p4RT spec example.
  RunPdWriteRpcStatusTest(
      "mix of successful and failed write update",
      gutil::ParseProtoOrDie<pdpi::WriteRpcStatus>(R"pb(
        rpc_response: {
          statuses: { code: 8 message: "Table is full." }
          statuses: { code: 0 }
          statuses: { code: 6 message: "Entity already exists." }

        }
      )pb"),
      3, pdpi::INPUT_IS_VALID);

  RunPdWriteRpcStatusTest(
      "all write failed", gutil::ParseProtoOrDie<pdpi::WriteRpcStatus>(R"pb(
        rpc_response: {
          statuses: { code: RESOURCE_EXHAUSTED message: "Table is full." }
          statuses: {
            code: INVALID_ARGUMENT
            message: "can not parse write request."
          }
          statuses: { code: ALREADY_EXISTS message: "entry already exists." }
        }
      )pb"),
      3, pdpi::INPUT_IS_VALID);
}

static void RunStreamMessageRequestTests(pdpi::IrP4Info info) {
  RunPiStreamMessageRequestTest(
      info, "unsupported update",
      gutil::ParseProtoOrDie<p4::v1::StreamMessageRequest>(R"pb(
        digest_ack { digest_id: 1 list_id: 3 }
      )pb"));

  RunPdStreamMessageRequestTest(
      info, "empty", gutil::ParseProtoOrDie<pdpi::StreamMessageRequest>(R"pb(
      )pb"),
      pdpi::INPUT_IS_INVALID);

  // Invalid packet values are tested in packet_io_test.cc.
  RunPdStreamMessageRequestTest(
      info, "arbitration",
      gutil::ParseProtoOrDie<pdpi::StreamMessageRequest>(R"pb(
        arbitration {
          device_id: 5314
          election_id { high: 0 low: 234123 }
          status { code: 0 }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);

  RunPdStreamMessageRequestTest(
      info, "packet", gutil::ParseProtoOrDie<pdpi::StreamMessageRequest>(R"pb(
        packet {
          payload: "1"
          metadata { submit_to_ingress: "0x1" egress_port: "eth-1/2/3" }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);
}

static void RunStreamMessageResponseTests(pdpi::IrP4Info info) {
  RunPiStreamMessageResponseTest(
      info, "unsupported update",
      gutil::ParseProtoOrDie<p4::v1::StreamMessageResponse>(R"pb(
        digest { digest_id: 1 list_id: 3 }
      )pb"));

  RunPdStreamMessageResponseTest(
      info, "empty", gutil::ParseProtoOrDie<pdpi::StreamMessageResponse>(R"pb(
      )pb"),
      pdpi::INPUT_IS_INVALID);

  // Invalid packet values are tested in packet_io_test.cc.
  RunPdStreamMessageResponseTest(
      info, "arbitration",
      gutil::ParseProtoOrDie<pdpi::StreamMessageResponse>(R"pb(
        arbitration {
          device_id: 5314
          election_id { high: 0 low: 234123 }
          status { code: 0 }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);

  RunPdStreamMessageResponseTest(
      info, "packet", gutil::ParseProtoOrDie<pdpi::StreamMessageResponse>(R"pb(
        packet {
          payload: "1"
          metadata { ingress_port: "0x034" target_egress_port: "eth-1/2/3" }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);

  RunPdStreamMessageResponseTest(
      info, "error", gutil::ParseProtoOrDie<pdpi::StreamMessageResponse>(R"pb(
        error {
          status { code: 1 message: "This is an error." }
          packet_out {
            payload: "1"
            metadata { submit_to_ingress: "0x1" egress_port: "eth-1/2/3" }
          }
        }
      )pb"),
      pdpi::INPUT_IS_VALID);
}

int main(int argc, char** argv) {
  // Usage: rpc_test <p4info file>.
  if (argc != 2) {
    std::cerr << "Invalid number of arguments." << std::endl;
    return 1;
  }
  const auto p4info =
      gutil::ParseProtoFileOrDie<p4::config::v1::P4Info>(argv[1]);

  absl::StatusOr<pdpi::IrP4Info> status_or_info = pdpi::CreateIrP4Info(p4info);
  if (!status_or_info.status().ok()) {
    std::cerr << "Unable to create IrP4Info." << std::endl;
    return 1;
  }
  pdpi::IrP4Info info = status_or_info.value();

  RunReadRequestTests(info);
  RunReadResponseTests(info);
  RunUpdateTests(info);
  RunWriteRequestTests(info);
  RunWriteRpcStatusTest();
  RunStreamMessageRequestTests(info);
  RunStreamMessageResponseTests(info);
  return 0;
}

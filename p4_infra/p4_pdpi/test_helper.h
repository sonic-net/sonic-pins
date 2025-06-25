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

#ifndef PINS_P4_INFRA_P4_PDPI_TEST_HELPER_H_
#define PINS_P4_INFRA_P4_PDPI_TEST_HELPER_H_

#include <functional>
#include <iostream>
#include <ostream>
#include <string>

#include "absl/functional/function_ref.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/message.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/translation_options.h"

namespace pdpi {

constexpr char kBanner[] =
    "=========================================================================";

enum InputValidity {
  INPUT_IS_VALID = 1,
  INPUT_IS_INVALID = 2,
};

inline std::string TestHeader(absl::string_view test_name) {
  return absl::StrCat(kBanner, "\n", test_name, "\n", kBanner);
}

inline void Fail(absl::string_view test_name, absl::string_view message) {
  // Splitting "DO NOT SUB***" into two pieces to avoid triggering our tools.
  std::cout << "TEST FAILED (DO NOT "
            << "SUBMIT)" << std::endl;
  std::cout << "TEST NAME: " << test_name << std::endl;
  std::cout << "FAILURE REASON: " << message << std::endl << std::endl;
}

// Dependencies on the exact output format of `Status::operator <<` are out
// of contract. We need a custom serialization function for golden-based tests.
inline std::string TestStatusToString(absl::Status status) {
  if (status.ok()) {
    return "OK";
  }
  return absl::StrCat(absl::StatusCodeToString(status.code()), ": ",
                      status.message());
}

// Runs a generic test starting from an invalid PI and checks that it cannot be
// translated to IR. If you want to test valid PI->IR, set 'validity' to
// INPUT_IS_VALID or preferably, if possible, use a generic pd test which
// provides greater coverage (PD->IR->PI->IR->PD + roundtrip property).
template <typename IR, typename PI>
void RunGenericPiTest(
    const pdpi::IrP4Info& info, const std::string& test_name, const PI& pi,
    pdpi::TranslationOptions options,
    absl::FunctionRef<absl::StatusOr<IR>(const pdpi::IrP4Info&, const PI&,
                                         pdpi::TranslationOptions options)>
        pi_to_ir,
    InputValidity validity = INPUT_IS_INVALID) {
  // Input and header.
  std::cout << TestHeader(test_name) << std::endl << std::endl;
  std::cout << "--- PI (Input):" << std::endl;
  std::cout << ::gutil::PrintTextProto(pi) << std::endl;

  // Convert PI to IR.
  const auto& ir = pi_to_ir(info, pi, options);
  if (!ir.ok()) {
    if (validity == INPUT_IS_VALID) {
      Fail(test_name,
           "Translation from PI to IR failed even though input was marked as "
           "valid).");
      std::cout << ir.status().message() << std::endl;
    } else {
      std::cout << "--- PI is invalid/unsupported:" << std::endl;
      std::cout << TestStatusToString(ir.status()) << std::endl;
    }
  } else {
    if (validity == INPUT_IS_INVALID) {
      Fail(
          test_name,
          "Translation from PI to IR succeeded even though input was marked as "
          "invalid");
      return;
    } else {
      std::cout << "--- IR:" << std::endl;
      std::cout << ::gutil::PrintTextProto(*ir) << std::endl;
    }
  }
  std::cout << std::endl;
}

// Runs a generic test starting from an invalid IR and checks that it cannot be
// translated to PI. If you want to test valid IR->PI, set 'validity' to
// INPUT_IS_VALID or preferably, if possible, use a generic pd test which
// provides greater coverage (PD->IR->PI->IR->PD + roundtrip property).
template <typename IR, typename PI>
void RunGenericIrToPiTest(
    const pdpi::IrP4Info& info, const std::string& test_name, const IR& ir,
    pdpi::TranslationOptions options,
    absl::FunctionRef<absl::StatusOr<PI>(const pdpi::IrP4Info&, const IR&,
                                         pdpi::TranslationOptions options)>
        ir_to_pi,
    InputValidity validity = INPUT_IS_INVALID) {
  // Input and header.
  std::cout << TestHeader(test_name) << std::endl << std::endl;
  std::cout << "--- IR (Input):" << std::endl;
  std::cout << ::gutil::PrintTextProto(ir) << std::endl;

  // Convert IR to PI.
  const auto& pi = ir_to_pi(info, ir, options);
  if (!pi.ok()) {
    if (validity == INPUT_IS_VALID) {
      Fail(test_name,
           "Translation from IR to PI failed even though input was marked as "
           "valid).");
      std::cout << pi.status().message() << std::endl;
    } else {
      std::cout << "--- IR (converting to PI) is invalid/unsupported:"
                << std::endl;
      std::cout << TestStatusToString(pi.status()) << std::endl;
    }
  } else {
    if (validity == INPUT_IS_INVALID) {
      Fail(
          test_name,
          "Translation from IR to PI succeeded even though input was marked as "
          "invalid");
    } else {
      std::cout << "--- PI:" << std::endl;
      std::cout << ::gutil::PrintTextProto(*pi) << std::endl;
    }
  }
  std::cout << std::endl;
}

// Runs a generic test starting from an invalid IR and checks that it cannot be
// translated to PD. If you want to test valid IR->PD, set 'validity' to
// INPUT_IS_VALID or preferably, if possible, use a generic pd test which
// provides greater coverage (PD->IR->PI->IR->PD + roundtrip property).
template <typename IR, typename PD>
void RunGenericIrToPdTest(
    const pdpi::IrP4Info& info, const std::string& test_name, const IR& ir,
    pdpi::TranslationOptions options,
    absl::FunctionRef<absl::Status(const pdpi::IrP4Info&, const IR&,
                                   google::protobuf::Message*,
                                   pdpi::TranslationOptions)>
        ir_to_pd,
    InputValidity validity = INPUT_IS_INVALID) {
  // Input and header.
  std::cout << TestHeader(test_name) << std::endl << std::endl;
  std::cout << "--- IR (Input):" << std::endl;
  std::cout << ::gutil::PrintTextProto(ir) << std::endl;

  // Convert IR to PD.
  PD pd;
  const auto& status_pd = ir_to_pd(info, ir, &pd, options);
  if (!status_pd.ok()) {
    if (validity == INPUT_IS_VALID) {
      Fail(test_name,
           "Translation from IR to PD failed even though input was marked as "
           "valid).");
      std::cout << status_pd.message() << std::endl;
    } else {
      std::cout << "--- IR (converting to PD) is invalid/unsupported:"
                << std::endl;
      std::cout << TestStatusToString(status_pd) << std::endl;
    }
  } else {
    if (validity == INPUT_IS_INVALID) {
      Fail(
          test_name,
          "Translation from IR to PD succeeded even though input was marked as "
          "invalid");
    } else {
      std::cout << "--- PD:" << std::endl;
      std::cout << ::gutil::PrintTextProto(pd) << std::endl;
    }
  }
  std::cout << std::endl;
}

// Runs a generic test starting from a valid PD entity. If pd is valid, then it
// is translated: PD -> IR -> PI -> IR2 -> PD2 and IR == IR2 and
// relevant_pd_fields(PD) == PD2 are checked.
template <typename PD, typename IR, typename PI>
void RunGenericPdTest(
    const pdpi::IrP4Info& info, const std::string& test_name, const PD& pd,
    pdpi::TranslationOptions options,
    absl::FunctionRef<absl::StatusOr<IR>(const pdpi::IrP4Info&, const PD&,
                                         pdpi::TranslationOptions options)>
        pd_to_ir,
    absl::FunctionRef<absl::Status(const pdpi::IrP4Info&, const IR&,
                                   google::protobuf::Message*,
                                   pdpi::TranslationOptions options)>
        ir_to_pd,
    absl::FunctionRef<absl::StatusOr<PI>(const pdpi::IrP4Info&, const IR&,
                                         pdpi::TranslationOptions options)>
        ir_to_pi,
    absl::FunctionRef<absl::StatusOr<IR>(const pdpi::IrP4Info&, const PI&,
                                         pdpi::TranslationOptions options)>
        pi_to_ir,
    absl::FunctionRef<absl::StatusOr<PI>(const pdpi::IrP4Info&, const PD&,
                                         pdpi::TranslationOptions options)>
        pd_to_pi,
    absl::FunctionRef<absl::Status(const pdpi::IrP4Info&, const PI&,
                                   google::protobuf::Message*,
                                   pdpi::TranslationOptions options)>
        pi_to_pd,
    const InputValidity& validity,
    absl::FunctionRef<PD(const pdpi::IrP4Info& info, const PD&,
                         pdpi::TranslationOptions options)>
        relevant_pd_fields =
            [](const pdpi::IrP4Info& info, const PD& pd,
               pdpi::TranslationOptions options) { return pd; }) {
  // Input and header.
  std::cout << TestHeader(test_name) << std::endl << std::endl;
  std::cout << "--- PD (Input):" << std::endl;
  std::cout << ::gutil::PrintTextProto(pd) << std::endl;

  // Set-up message differencer.
  google::protobuf::util::MessageDifferencer diff;
  diff.set_report_moves(false);
  diff.set_repeated_field_comparison(
      google::protobuf::util::MessageDifferencer::RepeatedFieldComparison::
          AS_SET);
  std::string explanation;
  diff.ReportDifferencesToString(&explanation);

  // Convert PD to IR.
  const auto& status_or_ir = pd_to_ir(info, pd, options);
  if (!status_or_ir.ok()) {
    if (validity == INPUT_IS_VALID) {
      Fail(test_name,
           "Translation from PD to IR failed even though input was marked as "
           "valid).");
      std::cout << status_or_ir.status().message() << std::endl;
      return;
    }
    std::cout << "--- PD is invalid/unsupported:" << std::endl;
    std::cout << TestStatusToString(status_or_ir.status()) << std::endl;
    return;
  }
  const auto& ir = status_or_ir.value();
  // Convert IR to PI.
  const auto& status_or_pi = ir_to_pi(info, ir, options);

  if (validity == INPUT_IS_INVALID) {
    if (status_or_pi.status().ok()) {
      Fail(test_name,
           "Input was marked as invalid, but translation from PD to IR and IR "
           "to PI both succeeded).");
      return;
    } else {
      std::cout << "--- PD is invalid/unsupported (detected when translating "
                   "IR to PI):"
                << std::endl;
      std::cout << status_or_pi.status().message() << std::endl;
      return;
    }
  }

  // At this point, validity == INPUT_IS_VALID
  std::cout << "--- IR:" << std::endl;
  std::cout << ::gutil::PrintTextProto(ir) << std::endl;
  if (!status_or_pi.status().ok()) {
    Fail(test_name,
         "Translation from IR to PI failed even though input was marked as "
         "valid).");
    std::cout << status_or_pi.status().message() << std::endl;
    return;
  }

  const auto& status_or_pi2 = pd_to_pi(info, pd, options);
  if (!status_or_pi2.ok()) Fail(test_name, "pd_to_pi failed.");

  const auto& pi = status_or_pi.value();
  std::cout << "--- PI:" << std::endl;
  std::cout << ::gutil::PrintTextProto(pi) << std::endl;

  // Convert PI back to IR.
  const auto& status_or_ir2 = pi_to_ir(info, pi, options);
  if (!status_or_ir2.status().ok()) {
    Fail(test_name, "Reverse translation from PI to IR failed.");
    std::cout << status_or_ir2.status().message() << std::endl;
    return;
  }
  if (!diff.Compare(ir, status_or_ir2.value())) {
    Fail(test_name,
         "Reverse translation from PI to IR resulted in a different IR.");
    std::cout << "Differences: " << explanation << std::endl;
    std::cout << "IR (after reverse translation):" << std::endl
              << ::gutil::PrintTextProto(status_or_ir2.value()) << std::endl;
    return;
  }

  // Convert IR back to PD.
  PD pd2;
  const auto& status_pd2 = ir_to_pd(info, ir, &pd2, options);
  if (!status_pd2.ok()) {
    Fail(test_name, "Reverse translation from IR to PD failed.");
    std::cout << status_pd2.message() << std::endl;
    return;
  }
  if (!diff.Compare(relevant_pd_fields(info, pd, options), pd2)) {
    Fail(test_name,
         "Reverse translation from IR to PD resulted in a different PD.");
    std::cout << "Differences: " << explanation << std::endl;
    std::cout << "PD (after reverse translation):" << std::endl
              << ::gutil::PrintTextProto(pd2) << std::endl;
    return;
  }

  PD pd3;
  const auto& status_pd3 = pi_to_pd(info, pi, &pd3, options);
  if (!status_pd3.ok()) Fail(test_name, "pi_to_pd failed.");

  std::cout << std::endl;
}

}  // namespace pdpi
#endif  // PINS_P4_INFRA_P4_PDPI_TEST_HELPER_H_

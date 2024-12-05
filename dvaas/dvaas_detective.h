// A library for explaining patterns in `PacketTestOutcomes` in a human-friendly
// way (see go/dvaas-detective).

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

#ifndef PINS_DVAAS_DVAAS_DETECTIVE_H_
#define PINS_DVAAS_DVAAS_DETECTIVE_H_

#include <string>
#include <variant>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "dvaas/dvaas_detective.pb.h"
#include "dvaas/test_vector.pb.h"
#include "yggdrasil_decision_forests/model/random_forest/random_forest.h"

namespace dvaas {
namespace dvaas_internal {

// Pretty printer for `DetectiveExplanation`.
std::string DetectiveExplanationToString(
    const DetectiveExplanation& explanation);

// Creates an `Explanation` from `rf_model`.
//  - `model` must have exactly one tree.
//  - `model` must have been created using the ydf library.
absl::StatusOr<DetectiveExplanation> ExtractExplanationFromModel(
    const yggdrasil_decision_forests::model::random_forest::RandomForestModel&
        model);

// Converts `test_outcomes` to CSV data and writes it to a temporary file.
// Returns path of temporary file on success. Returns error if temporary file
// cannot be created.
// - CSV data is created using `TestOutcomeToFeatureMap`.
absl::StatusOr<std::string> WriteTempCsvFileFromPacketTestOutcomes(
    const PacketTestOutcomes& test_outcomes);

// Semantics for numerical features:
// https://ydf.readthedocs.io/en/latest/guide_feature_semantics/#ydfsemanticnumerical
using NumericalValue = float;

// Semantics for categorical features:
// https://ydf.readthedocs.io/en/latest/guide_feature_semantics/#ydfsemanticcategorical
using CategoricalValue = std::string;

// Feature values can have different types, each having it's own semantics.
// https://ydf.readthedocs.io/en/latest/guide_feature_semantics
using FeatureValue = std::variant<NumericalValue, CategoricalValue>;

// Returns `value` as a printable string.
std::string FeatureValueToString(const FeatureValue& value);

// Returns list of feature names used by DVaaS Detective.
std::vector<absl::string_view> GetListOfFeatureNames();

// Returns map from feature names to feature values extracted from
// `test_outcome`. List of feature names can be obtained using
// `GetListOfFeatureNames`.
absl::flat_hash_map<std::string, FeatureValue> TestOutcomeToFeatureMap(
    const PacketTestOutcome& test_outcome);

}  // namespace dvaas_internal
}  // namespace dvaas

#endif  // PINS_DVAAS_DVAAS_DETECTIVE_H_

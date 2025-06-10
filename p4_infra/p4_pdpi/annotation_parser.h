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

#ifndef PINS_P4_INFRA_P4_PDPI_ANNOTATION_PARSER_H_
#define PINS_P4_INFRA_P4_PDPI_ANNOTATION_PARSER_H_

#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/status.h"

// This header file defines libraries for parsing P4 annotations.
//
// Valid P4 annotations have the following format:
//   @<label>(<body>)
// Examples:
//   @sai_acl(INGRESS)
//   $sai_action(SAI_PACKET_ACTION_DROP, RED)
//
// P4 annotations ignore spaces within the parentheses and between the label and
// first parenthesis. For example,
//   @sai_acl(INGRESS) is treated the same as @sai_acl (  INGRESS )

namespace pdpi {

namespace annotation {
// Template type definition of a parser function to be used in GetAnnotation and
// GetAllAnnotations. The parser function will be called with the body of a
// matching annotation.
template <typename T>
using BodyParser = std::function<absl::StatusOr<T>(std::string)>;

// Parses a string of the format: "arg [, arg2] [, arg3] [, ...]" into separate,
// ordered arguments. Returned arguments are stripped of whitespace except for
// whitespace within a string boundary (" ").
// Results are tokenized to ensure that any nested (*) {*} [*] or "*" are kept
// together. No escaping is supported.
absl::StatusOr<std::vector<std::string>> ParseAsArgList(std::string value);

// Returns the raw input string.
inline absl::StatusOr<std::string> Raw(std::string body) { return body; }

struct AnnotationComponents {
  std::string label;
  std::string body;
};
}  // namespace annotation

// Parses an annotation into the AnnotationComponents.
// Returns an InvalidArgument error if parsing failed.
absl::StatusOr<annotation::AnnotationComponents> ParseAnnotation(
    const std::string& annotation);

// Returns a list of all annotations split into label & body.
// Skips annotations that do not follow the expected @<label>(<body>) format.
template <typename Container>
std::vector<annotation::AnnotationComponents> GetAllAnnotations(
    const Container& annotations) {
  std::vector<annotation::AnnotationComponents> components;
  for (const auto& annotation : annotations) {
    auto parser_result = ParseAnnotation(annotation);
    if (parser_result.ok()) {
      components.push_back(std::move(*parser_result));
    }
  }
  return components;
}

// Returns a list of the parsed body of all annotations with the given label.
//
// Note: Currently, template type deduction does not work for this function. To
// use GetAllParsedAnnotations, declare it with the parser's StatusOr<T> T type.
// Example:
//   absl::StatusOr<int>(std::string> ps) parser;
//   ASSIGN_OR_RETURN(auto result,
//                    GetAllParsedAnnotations<int>(label, annotations, parser);
template <typename T, typename Container>
absl::StatusOr<std::vector<T>> GetAllParsedAnnotations(
    absl::string_view label, const Container& annotations,
    annotation::BodyParser<T> parser) {
  std::vector<T> values;
  for (const auto& annotation : annotations) {
    auto parser_result = ParseAnnotation(annotation);
    if (!parser_result.ok()) continue;  // Skip unknown labels.

    const annotation::AnnotationComponents& parsed_annotation =
        parser_result.value();
    if (parsed_annotation.label == label) {
      ASSIGN_OR_RETURN(
          T value, parser(std::move(parsed_annotation.body)),
          _ << "Failed to parse annotation \"" << annotation << "\"");
      values.push_back(value);
    }
  }
  return values;
}

// Returns the parsed body of the unique annotation with the given label.
// Returns a Status with code kNotFound if there is no matching annotation.
// Returns a Status with code kInvalidArgument if there are multiple matching
// annotations.
//
// Note: Currently, template type deduction does not work for this function. To
// use GetAnnotation, declare it with the parser's StatusOr<T> T type.
// Example:
//   absl::StatusOr<int>(std::string> s) parser;
//   ASSIGN_OR_RETURN(int result,
//                    GetParsedAnnotation<int>(label, annotations, parser);
template <typename T, typename Container>
absl::StatusOr<T> GetParsedAnnotation(absl::string_view label,
                                      const Container& annotations,
                                      annotation::BodyParser<T> parser) {
  // Add extra parentheses around GetAllParsedAnnotations to prevent the
  // precompiler from splitting GetAllParsedAnnotations<T into its own argument.
  ASSIGN_OR_RETURN(auto values, (GetAllParsedAnnotations<T, Container>(
                                    label, annotations, parser)));
  if (values.empty()) {
    return gutil::NotFoundErrorBuilder()
           << "No annotations contained label \"" << label << "\"";
  }
  if (values.size() > 1) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Multiple annotations contained label \"" << label << "\"";
  }
  return values[0];
}

// Returns the body of an annotation with the unique label as a list of strings.
// Returns an empty list if the matching annotation has no arguments.
// Returns a Status with code kNotFound if there is no matching annotation.
template <typename Container>
absl::StatusOr<std::vector<std::string>> GetAnnotationAsArgList(
    absl::string_view label, const Container& annotations) {
  return GetParsedAnnotation<std::vector<std::string>>(
      label, annotations, annotation::ParseAsArgList);
}

// Returns the string list form of the body of all annotations with the given
// label.
template <typename Container>
absl::StatusOr<std::vector<std::vector<std::string>>>
GetAllAnnotationsAsArgList(absl::string_view label,
                           const Container& annotations) {
  return GetAllParsedAnnotations<std::vector<std::string>>(
      label, annotations, annotation::ParseAsArgList);
}

// Returns the body of an annotation with the given label.
// Returns a Status with code kNotFound if there is no matching annotation.
template <typename Container>
absl::StatusOr<std::string> GetAnnotationBody(absl::string_view label,
                                              const Container& annotations) {
  return GetParsedAnnotation<std::string>(label, annotations, annotation::Raw);
}

// Returns all annotation bodies from all annotations with the given label.
template <typename Container>
absl::StatusOr<std::vector<std::string>> GetAllAnnotationBodies(
    absl::string_view label, const Container& annotations) {
  return GetAllParsedAnnotations<std::string>(label, annotations,
                                              annotation::Raw);
}

}  // namespace pdpi

#endif  // PINS_P4_INFRA_P4_PDPI_ANNOTATION_PARSER_H_

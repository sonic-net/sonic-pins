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

#include "p4_pdpi/utils/annotation_parser.h"

#include <stack>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/str_split.h"
#include "gutil/status.h"

namespace pdpi {
namespace {
inline bool IsWhitespace(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}
}  // namespace

// Use a custom parser for improved speed and error reporting compared to a
// regex-based parser.
absl::StatusOr<annotation::AnnotationComponents> ParseAnnotation(
    const std::string& annotation) {
  //      Expected format (label + body): '@label(body)'
  // Allowable whitespace (label + body): '  @label  (body)  '
  //      Expected format (label-only): '@label'
  // Allowable whitespace (label-only): '  @label  '
  //
  // Whitespace consists of spaces (' ') and tabs ('\t').

  // Skip beginning whitespace.
  // (label + body): '  @label  (body)  ' --> '@label (body)  '
  //   (label-only): '  @label  ' --> '@label  '
  auto annotation_iter = annotation.begin();
  while (annotation_iter != annotation.end() &&
         IsWhitespace(*annotation_iter)) {
    ++annotation_iter;
  }
  // Move to the start of the label.
  // (label + body): '@label  (body)  ' --> 'label (body)  '
  //   (label-only): '@label  ' --> 'label  '
  if (annotation_iter == annotation.end() || *annotation_iter != '@') {
    return gutil::InvalidArgumentErrorBuilder()
           << "Annotation \"" << annotation << "\" is malformed: "
           << "Annotations must begin with '@'";
  }
  ++annotation_iter;

  // Process the label.
  // (label + body): 'label  (body)  ' --> ' (body)  ', capture label
  //   (label-only): 'label  ' --> '  ', capture label
  const auto label_start_iter = annotation_iter;
  while (annotation_iter != annotation.end() &&
         !IsWhitespace(*annotation_iter) && *annotation_iter != '(' &&
         *annotation_iter != ')') {
    ++annotation_iter;
  }
  if (annotation_iter == label_start_iter) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Annotation \"" << annotation << "\" is malformed: "
           << "Annotation contains no label text";
  }
  std::string label(label_start_iter, annotation_iter);

  // Skip whitespace.
  // (label + body): ' (body)  ' --> '(body)  '
  //   (label-only): '  ' --> ''
  while (annotation_iter != annotation.end() &&
         IsWhitespace(*annotation_iter)) {
    ++annotation_iter;
  }
  //   (label-only): Return label.
  if (annotation_iter == annotation.end()) {
    return annotation::AnnotationComponents({.label = std::move(label)});
  }
  // Move to the start of the annotation body.
  // '(body)  ' --> 'body)  '
  if (*annotation_iter != '(') {
    return gutil::InvalidArgumentErrorBuilder()
           << "Annotation \"" << annotation << "\" is malformed: "
           << "Expected '(' but found '" << *annotation_iter << "'";
  }
  ++annotation_iter;
  const auto body_start_iter = annotation_iter;

  // Process the annotation body.
  // Process from back->front looking for )

  // Skip whitespace.
  // 'body)  ' --> 'body)'
  annotation_iter = annotation.end();
  --annotation_iter;
  while (annotation_iter > body_start_iter && IsWhitespace(*annotation_iter)) {
    --annotation_iter;
  }
  // Move to the end of the annotation body.
  // 'body)' --> 'body'
  if (*annotation_iter != ')') {
    return gutil::InvalidArgumentErrorBuilder()
           << "Annotation \"" << annotation << "\" is malformed: "
           << "Missing ')' at the end of the annotation";
  }
  std::string body(body_start_iter, annotation_iter);

  return annotation::AnnotationComponents(
      {.label = std::move(label), .body = std::move(body)});
}

namespace annotation {
// Parses an annotation value and returns the component arguments in order.
absl::StatusOr<std::vector<std::string>> ParseAsArgList(std::string value) {
  std::vector<std::string> tokens;
  std::stack<char> scope;
  std::string token;
  for (const char c : value) {
    if (scope.empty() && c == ',') {
      tokens.push_back(token);
      token.clear();
      continue;
    } else if (!scope.empty() && c == scope.top()) {
      scope.pop();
    } else if (scope.empty() || scope.top() != '"') {
      switch (c) {
        case '(':
          scope.push(')');
          break;
        case '[':
          scope.push(']');
          break;
        case '{':
          scope.push('}');
          break;
        case '"':
          scope.push('"');
          break;
        case '\t':
        case ' ':
        case '\n':
        case '\r':
          continue;
        case ')':
        case ']':
        case '}':
          return gutil::InvalidArgumentErrorBuilder()
                 << "Malformed input. No matching character found for '" << c
                 << "'";
        default:
          break;
      }
    }
    token.push_back(c);
  }
  if (!scope.empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Malformed input. Expected '" << scope.top()
           << "' before end of string";
  }
  if (tokens.empty() && token.empty()) return tokens;
  tokens.push_back(token);
  return tokens;
}

}  // namespace annotation
}  // namespace pdpi

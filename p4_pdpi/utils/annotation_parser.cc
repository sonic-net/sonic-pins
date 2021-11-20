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
#include "re2/re2.h"

namespace pdpi {
namespace annotation {

namespace internal {
absl::StatusOr<AnnotationComponents> ParseAnnotation(
    const std::string& annotation) {
  // Regex: @<label>
  static constexpr LazyRE2 kLabelOnlyParser = {R"([ \t]*@([^ \t()]*)[ \t]*)"};
  // Regex: @<label> *(<&body>)
  static constexpr LazyRE2 kParser = {
      R"([ \t]*@([^ \t(]*)[ \t]*\((.*)\)[ \t]*)"};
  std::string label, body;

  if (RE2::FullMatch(annotation, *kLabelOnlyParser, &label)) {
    return AnnotationComponents({.label = std::move(label)});
  }
  if (RE2::FullMatch(annotation, *kParser, &label, &body)) {
    if (label.empty() && body.empty()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Annotation \"" << annotation << "\" is malformed";
    }
    return AnnotationComponents(
        {.label = std::move(label), .body = std::move(body)});
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "Annotation \"" << annotation << "\" is malformed";
}
}  // namespace internal

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

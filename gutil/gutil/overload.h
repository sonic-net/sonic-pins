// Copyright 2021 Google LLC
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

#ifndef PINS_GUTIL_GUTIL_OVERLOADED_H_
#define PINS_GUTIL_GUTIL_OVERLOADED_H_

#include <utility>

namespace gutil {

// Useful in conjunction with {std,absl}::visit.
// See https://en.cppreference.com/w/cpp/utility/variant/visit.
template <class... Ts>
struct Overload : Ts... {
  using Ts::operator()...;
  // Before C++20, we need a constructor to allow for using parenthesis instead
  // of curly braces.
  explicit Overload(Ts... ts) : Ts(std::move(ts))... {}
};
template <class... Ts>
Overload(Ts...) -> Overload<Ts...>;

}  // namespace gutil

#endif  // PINS_GUTIL_GUTIL_OVERLOADED_H_

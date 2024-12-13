#!/bin/bash
# Copyright 2025 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Formats source files according to Google's style guide. Requires clang-format.

# Only files with these extensions will be formatted by clang-format.
CLANG_FORMAT_EXTENSIONS="cc|h|proto"

# Run clang-format.
find . \
  | egrep "\.(${CLANG_FORMAT_EXTENSIONS})\$" \
  | xargs clang-format -style=google -i

# Run Buildifier.
bazel run :buildifier

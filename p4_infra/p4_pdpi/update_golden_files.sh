#!/bin/bash
# Copyright 2021 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Updates all golden files.
bazel run //third_party/pins_infra/p4_infra/p4_pdpi:p4info_diff_test -- --update
bazel run //third_party/pins_infra/p4_infra/p4_pdpi:table_entry_diff_test -- --update
bazel run //third_party/pins_infra/p4_infra/p4_pdpi:packet_io_diff_test -- --update
bazel run //third_party/pins_infra/p4_infra/p4_pdpi:references_diff_test -- --update
bazel run //third_party/pins_infra/p4_infra/p4_pdpi:rpc_diff_test -- --update
bazel run //third_party/pins_infra/p4_infra/p4_pdpi:main_pd_diff_test -- --update
bazel run //third_party/pins_infra/p4_infra/p4_pdpi:sequencing_diff_test -- --update

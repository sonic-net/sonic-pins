# Copyright 2023 Google LLC
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

"""This file includes macros for compiling P4 programs."""

load("@com_github_p4lang_p4c//:bazel/p4_library.bzl", "p4_library")

def p4_config_and_p4info_files(name, srcs, deps):
    """
    Macro that defines the compilation rules for provided P4 programs.

    Args:
        name: Name of the macro.
        srcs: List of P4 program sources.
        deps: List of P4 dependencies (included files).
    """
    for p4_src_path in srcs:
        p4c_name = p4_src_path.removesuffix(".p4")
        config_path = "%s.config.json" % p4c_name
        p4info_path = "%s.p4info.pb.txt" % p4c_name
        p4_library(
            name = p4c_name,
            src = p4_src_path,
            p4info_out = p4info_path,
            target = "bmv2",
            target_out = config_path,
            deps = deps,
        )

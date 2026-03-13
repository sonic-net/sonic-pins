# Copyright 2024 Google LLC
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

"""Test rules for IR

This file contains rule definitions for running the test binary to produce
output json and protobuf files, subset diff the input and output json files, and
golden file testing the output protobuf files against the expected files.
It also defines a Macro that simplifies defining a protobuf test over a sample
P4 program.
"""

load("@com_github_p4lang_p4c//:bazel/p4_library.bzl", "p4_library")
load("//gutil/gutil:diff_test.bzl", "diff_test")

def ir_parsing_test(name, p4_program, golden_file, table_entries = None, p4_deps = []):
    """Macro that defines exact diff IR testing rules for a given p4 program.

    The macro defines these rules in order:
    1. A rule for producing bmv2 json and p4info files from a .p4 file using p4c.
    2. A rule for parsing the bmv2 json and p4info using p4_symbolic/main.cc,
       and dumping a protobuf output file.
    3. A rule for golden file testing of the protobuf output file against the
       specified expected file.
    Use the p4_deps list to specify dependent files that p4_program input fle
    depends on (e.g. by including them).

    Args:
      name: Test name.
      p4_program: Input P4 program.
      golden_file: File containing the expected IR output.
      table_entries: File containing the table entries as input in protobuf text.
      p4_deps: List of targets that the P4 program depends on (e.g., included files)
    """
    bmv2_file = "tmp/%s.bmv2.json" % name
    p4info_file = "tmp/%s.p4info.pb.txt" % name
    test_output_file = "tmp/%s_output" % name

    # Run p4c to get bmv2 JSON and p4info.pb.txt files.
    tmp_bmv2_file = "%s.tmp" % bmv2_file
    p4_library(
        name = "%s_p4_library" % name,
        src = p4_program,
        deps = p4_deps,
        target = "bmv2",
        target_out = tmp_bmv2_file,
        p4info_out = p4info_file,
    )
    native.genrule(
        name = "%s_strip_files_paths_for_portability" % name,
        visibility = ["//visibility:private"],
        srcs = [tmp_bmv2_file],
        outs = [bmv2_file],
        cmd = """sed -e 's|"[^"]*\\.p4"|""|g' $(SRCS) > $(OUTS)""",
    )

    # Use p4_symbolic/ir/test.cc to parse input json with p4info and dump
    # (tmp) output.
    native.genrule(
        name = "%s_parse" % name,
        srcs = [
            bmv2_file,
            p4info_file,
        ] + ([table_entries] if table_entries else []),
        outs = [test_output_file],
        tools = ["//p4_symbolic/ir:test"],
        cmd = " ".join([
            "$(location //p4_symbolic/ir:test)",
            ("--bmv2=$(location %s)" % bmv2_file),
            ("--p4info=$(location %s)" % p4info_file),
            ("--entries=$(location %s)" % table_entries if table_entries else ""),
            ("--output=$(location %s)" % test_output_file),
            "|| true",
            # The following line makes sure hexstrings are lowercase in the
            # protobuf file. This is needed because the hexstring representation
            # of boost::multiprecision::cpp_int seems to behave differently
            # across different versions of boost (although the root cause has
            # not been fully investigated).
            "&& sed -i 's/0x[0-9A-F]\\+/\\L&/g' $(location %s)" % test_output_file,
        ]),
    )

    # Exact diff test between output and golden protobuf files.
    diff_test(
        name = name,
        actual = test_output_file,
        expected = golden_file,
    )

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

"""Rules for testing p4-symbolic.

This file contains rule definitions for running
the test binary to produce output json and protobuf files,
subset diff the input and output json files, and golden file
testing the output protobuf files against the expected files.
It also defines a Macro that simplifies defining a protobuf test
over a sample P4 program.
"""

load("@com_github_p4lang_p4c//:bazel/p4_library.bzl", "p4_library")
load("//p4_infra/p4_pdpi/testing:diff_test.bzl", "diff_test")

def end_to_end_test(
        name,
        p4_program,
        packets_golden_file,
        smt_golden_file,
        table_entries = None,
        port_count = 2,
        p4_deps = []):
    """
    Macro that defines our end to end tests.

    Given a p4 program, this macro runs our main binary
    on the p4 program and its table entries (if they exist).
    The binary outputs a debugging dump of the underlying smt program,
    as well as the output test packets.
    The macro compares both of these outputs against the provided
    expected golden files.
    The macro defines these rules in order:
    1. A rule for producing bmv2 json and p4info files from a .p4 file using p4c.
    2. A rule for running the main binary on the inputs using p4_symbolic/main.cc,
       and dumping both output files.
    3. Two rules for golden file testing of the two output files.
    4. A test suite combining the two rules above with the same name
       as given to the macro.
    Use the p4_deps list to specify dependent files that p4_program input
    file depends on (e.g. by including them).

    Args:
      name: Test name.
      p4_program: Input P4 program.
      packets_golden_file: File containing the expected concrete packets.
      smt_golden_file: File containing the expected SMT formulae.
      table_entries: File containing the table entries as input in protobuf text.
      port_count: Number of ports.
      p4_deps: List of targets that the P4 program depends on (e.g., included files).
    """
    p4c_name = "%s_p4c" % name
    p4info_file = "%s_bazel-p4c-tmp-output/p4info.pb.txt" % p4c_name
    packets_test_name = "%s_packets" % name
    smt_test_name = "%s_smt" % name

    bmv2_file = "tmp/%s.bmv2.json" % name
    p4info_file = "tmp/%s.p4info.pb.txt" % name

    # Run p4c to get bmv2 JSON and p4info.pb.txt files.
    tmp_bmv2_file = "%s.tmp" % bmv2_file
    p4_library(
        name = p4c_name,
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

    # Use p4_symbolic/main.cc to run our tool on the p4 program
    # and produce a debugging smt file and an output file with
    # interesting testing packets.
    packets_output_file = "generated/%s.txt" % name
    smt_output_file = "generated/%s.smt2" % name
    native.genrule(
        name = "%s_test_runner" % name,
        srcs = [
            bmv2_file,
            p4info_file,
        ] + ([table_entries] if table_entries else []),
        outs = [packets_output_file, smt_output_file],
        tools = ["//p4_symbolic:main"],
        cmd = " ".join([
            "$(location //p4_symbolic:main)",
            ("--bmv2=$(location %s)" % bmv2_file),
            ("--p4info=$(location %s)" % p4info_file),
            ("--entries=$(location %s)" % table_entries if table_entries else ""),
            ("--packets=$(location %s)" % packets_output_file),
            ("--smt=$(location %s)" % smt_output_file),
            ("--port_count=%d" % port_count),
        ]),
    )

    # Exact diff test for the packet output file.
    diff_test(
        name = packets_test_name,
        actual = packets_output_file,
        expected = packets_golden_file,
    )

    # Group tests into a test_suite with the given name.
    # This is just to make the provided name alias to something.
    native.test_suite(
        name = name,
        tests = [
            (":%s" % packets_test_name),
        ],
    )

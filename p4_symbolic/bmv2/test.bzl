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

"""Rules for testing BMv2 parser.

This file contains rule definitions for running
the test binary to produce output json and protobuf files,
subset diff the input and output json files, and golden file
testing the output protobuf files against the expected files.
It also defines a Macro that simplifies defining a protobuf test
over a sample P4 program.
"""

load("@com_github_p4lang_p4c//:bazel/p4_library.bzl", "p4_library")
load("//p4_infra/p4_pdpi/testing:diff_test.bzl", "diff_test")

def _subset_diff_impl(ctx):
    """Subset diff between actual and expected json files.

    The actual must be a subset of the expected.
    """
    ctx.actions.write(
        output = ctx.outputs.executable,
        is_executable = True,
        content = "python {sdiff_py} {expected} {actual}".format(
            sdiff_py = ctx.file._sdiff_py.short_path,
            expected = ctx.file.expected.short_path,
            actual = ctx.file.actual.short_path,
        ),
    )

    runfiles = [ctx.file._sdiff_py, ctx.file.actual, ctx.file.expected]
    return DefaultInfo(
        runfiles = ctx.runfiles(files = runfiles),
    )

subset_diff_test = rule(
    doc = """
        Computes a smart subset diff between two JSON objects.

        A subset diff is defined as follows:
        1. We allow every sub-dict in the expected file to contain additional
        keys that the actual file does not contain, but not the other way
        around. This should hold recursively.
        2. For leaf fields present in both files, that are primitive types
        (e.g. strings or numbers), their values must be equal.
        3. Corresponding lists must have the same number of elements (no
        sublists), and corresponding elements (index-wise) must satisify the
        subset relation.
        4. Finally, null/undefined values in the expected files are accepted
        to be equal to default values in actual of their respective types
        (e.g. "", []).

        Rational:
        1. Our protobuf definitions being tested here are incomplete: we
           intentionally ignore certain fields that are not useful to our tool.
           This means that in many cases, actual != expected.
        2. This behavior is not exhibited with lists: either protobuf parses
           the entire list when its part of the definition, or ignores it
           completely if it is not defined.
        3. Any null values in the expected json is parsed by protobuf as a
           default value of the corresponding type (e.g. 0 for ints). Our
           tool can either find out that the default value is a placeholder
           for null using the context, or does not exhibit a semnatic difference
           between null and the default value for the particular field.

        This rule takes a single argument: input.
        This is the json input file, or a rule that produces this json input
        file. The rule passes this input file in to the compiled
        p4_symbolic/main.cc which parses it with protobuf and then dumps it
        back to JSON.

        The rule checks that the dumped output (called actual) is a proper
        subset of the input (called exact).
        """,
    implementation = _subset_diff_impl,
    test = True,
    attrs = {
        "actual": attr.label(
            doc = "The dumped protobuf JSON file, or a rule producing it.",
            mandatory = True,
            allow_single_file = True,
        ),
        "expected": attr.label(
            doc = """
                The original input json file (produced by p4c), or a
                rule producing it.
                """,
            mandatory = True,
            allow_single_file = True,
        ),
        "_sdiff_py": attr.label(
            doc = "The diff python script file.",
            mandatory = False,
            allow_single_file = True,
            default = "test_sdiff.py",
        ),
    },
)

def bmv2_protobuf_parsing_test(name, p4_program, golden_file, p4_deps = []):
    """Macro that defines subset and exact diff rules for a given p4 program
    with all their dependent rules.

    The macro defines these exact rules, in this logical order of dependencies:
    1. A rule for producing bmv2 json from a .p4 program using p4c.
    2. A rule for parsing the bmv2 json using p4_symbolic/bmv2/test.cc, and
       dumping a protobuf and json output files.
    3. A rule for golden file testing of the protobuf output file against
       the specified expected file.
    4. A rule for subset diff testing of json output file (subset) against
       the output of p4c (superset).
    5. A test suite combining both 4 and 5.
    Use the p4_deps list to specify dependent files that p4_program input
    file depends on (e.g. by including them).
    """
    p4c_name = "%s_p4c" % name
    bmv2_json = "%s.bmv2.json" % name
    tmp_bmv2_json = "%s.tmp" % bmv2_json
    parse_name = "%s_parse" % name
    exact_diff_name = "%s_exact_test" % name
    subset_diff_name = "%s_subset_test" % name

    # Run p4c to get bmv2 input .json file.
    p4_library(
        name = p4c_name,
        src = p4_program,
        deps = p4_deps,
        target = "bmv2",
        target_out = tmp_bmv2_json,
    )

    native.genrule(
        name = "%s_strip_files_paths_for_portability" % name,
        visibility = ["//visibility:private"],
        srcs = [tmp_bmv2_json],
        outs = [bmv2_json],
        cmd = """sed -e 's|"[^"]*\\.p4"|""|g' $(SRCS) > $(OUTS)""",
    )

    # Use p4_symbolic/bmv2/test.cc to parse input json and dump
    # (tmp) output .pb.txt and .json files.
    proto_filename = name + "_tmp.pb.txt"
    json_filename = name + "_tmp.json"

    native.genrule(
        name = parse_name,
        srcs = [bmv2_json],
        outs = [proto_filename, json_filename],
        tools = ["//p4_symbolic/bmv2:test"],
        cmd = " ".join([
            "$(location //p4_symbolic/bmv2:test)",
            ("--bmv2=$(location %s)" % bmv2_json),
            ("--protobuf=$(location %s)" % proto_filename),
            ("--json=$(location %s)" % json_filename),
            # The following line makes sure hexstrings are lowercase in the protobuf file.
            # This is needed because the hexstring representation of boost::multiprecision::cpp_int
            # seems to behave differently accross different versions of boost (although the root
            # cause has not been fully investigated).
            "&& sed -i 's/0x[0-9A-F]\\+/\\L&/g' $(location %s)" % proto_filename,
        ]),
    )

    # Subset diff test between output and input json files
    subset_diff_test(
        name = subset_diff_name,
        actual = json_filename,
        expected = bmv2_json,
    )

    # Exact diff test between output and golden protobuf files.
    diff_test(
        name = exact_diff_name,
        actual = proto_filename,
        expected = golden_file,
    )

    # Group tests into a test_suite with the given name.
    # This is just to make the provided name alias to something.
    native.test_suite(
        name = name,
        tests = [
            ":" + subset_diff_name,
            ":" + exact_diff_name,
        ],
    )

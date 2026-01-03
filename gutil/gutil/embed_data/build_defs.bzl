# Copyright 2019 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Embeds data files into a C++ or Go module."""

def clean_dep(dep):
    """Returns an absolute Bazel path to 'dep'.

    This is necessary when calling these functions from another workspace.
    """
    return str(Label(dep))

def cc_embed_data(
        name,
        srcs,
        cc_file_output,
        h_file_output,
        testonly = False,
        cpp_namespace = None,
        strip_prefix = None,
        flatten = False,
        identifier = None,
        **kwargs):
    """Embeds 'srcs' into a C++ module.

    Generates a header like:
      namespace gutil {
        struct FileToc {
          const char* name;             // the file's original name
          const char* data;             // beginning of the file
          size_t size;                  // length of the file
        };
      }
      namespace foo {
      extern const struct ::gutil::FileToc* this_rule_name_create();
      }
    The 'this_rule_name()' function will return an array of FileToc
    structs terminated by one that has nullptr 'name' and 'data' fields.
    The 'data' field always has an extra null terminator at the end (which
    is not included in the size).
    Args:
      name: The rule name, which will also be the identifier of the generated
        code symbol.
      srcs: List of files to embed.
      cc_file_output: The CC implementation file to output.
      h_file_output: The H header file to output.
      testonly: If True, only testonly targets can depend on this target.
      cpp_namespace: Wraps everything in a C++ namespace.
      strip_prefix: Strips this verbatim prefix from filenames (in the TOC).
      flatten: Removes all directory components from filenames (in the TOC).
      identifier: The identifier to use in generated names (defaults to name).
      **kwargs: Args to pass to the cc_library.
    """
    generator = clean_dep("//gutil/gutil/embed_data:generate_cc_embed_data")
    generator_location = "$(location %s)" % generator
    if identifier == None:
        identifier = name
    flags = "--output_header='$(location %s)' --output_impl='$(location %s)'" % (
        h_file_output,
        cc_file_output,
    )
    flags += " --identifier='%s'" % (identifier,)
    if cpp_namespace != None:
        flags += " --cpp_namespace='%s'" % (cpp_namespace,)
    if strip_prefix != None:
        flags += " --strip_prefix='%s'" % (strip_prefix,)
    if flatten:
        flags += " --flatten"

    native.genrule(
        name = name + "__generator",
        srcs = srcs,
        outs = [
            cc_file_output,
            h_file_output,
        ],
        tools = [generator],
        cmd = "%s $(SRCS) %s" % (generator_location, flags),
        testonly = testonly,
    )
    native.cc_library(
        name = name,
        hdrs = [h_file_output],
        srcs = [cc_file_output],
        testonly = testonly,
        **kwargs
    )

def go_embed_data(
        name,
        package,
        var,
        out = None,
        src = None,
        srcs = None,
        flatten = 0,
        string = 0,
        testonly = None,
        visibility = None,
        compatible_with = None):
    """go_embed_data generates a Go source file encoding to an embedded data file.

    Generate a Go source file containing a []byte or string variable
    containing the data in the specified sources.  E.g., a
    comma-separated values file will be available as a single byte
    array with the given variable name.  Read below for how multiple
    data files are handled.

    Backslashes and double quotation marks in the input are escaped.

    Args:
      name: Name of the rule, as a string.
      package: Name of the Go package for the generated variable(s),
        as a string.
      var: The desired name of the generated file's variable, as a
        string.  Alternatively, if a key-value pair '{"mydata1":
        "mydata1.png", "mydata2": "mydata2.png"}', then the generated file
        will contain one variable for each key, e.g., "mydata1", with type
        []byte or string and assigned the corresponding file
        contents, e.g., in "mydata1.png".
      out: The name of the created file relative to the current directory.
        If out is not provided, the output will be name + ".go". It is
        strongly recommended that an explicit out is provided, as
        tooling (e.g., glaze) may look at this parameter. The implicit
        parameter form is supported only for compatibility with bazel go
        rules in special cases.
      src: A label for a single file of data.  Its contents are
        available as a []byte or a string, depending on the value of
        "string".  If specified, "srcs" should be unspecified.
      srcs: A list of labels specifying multiple files of
        data. Alternatively, a rule with multiple outputs or a glob.
        var's type will be map[string][]byte or map[string]string,
        depending on the value of "string".  Keys will be google3-relative
        filenames.  E.g., a label "go_tools.blueprint" in the
        "google3/go/tools" directory will have a filename
        "go/tools/go_tools.blueprint".  If specified, "src" should be
        unspecified.
      flatten: If True, the filenames in the generated map will be the
        basename of their full names. This is useful when embedding
        the output of another rule.
      string: If True, the generated variable declarations will have
        "string" type, not "[]byte".
      testonly: If True, only testonly targets, e.g., tests can depend
        on this target.  Q.v., go/be#common.testonly.
      visibility: List of visibility labels controlling which packages
        can acesss this rule.  Q.v., go/visibility.
      compatible_with: List of environment labels for which the rule
        can be built.  Q.v., go/be#common.compatible_with.

    Sample usage:
      load("//go/tools:build_defs.bzl", "go_embed_data")
      go_embed_data(
          name = "gen_mydata",
          src = "mydata.png",
          out = "mydata.go",
          package = "mypkg",
          var = "mydata",
      )
      go_library(
          name = "mypkg",
          srcs = [
              "other_src.go", # Assigns the "mypkg.mydata" variable to
                              # access mydata.png's contents.
              "mydata.go",    # Generated by gen_mydata.
          ],
      )
    """
    more_args = ""
    if type(var) == type({}):
        if src or srcs:
            fail("go_embed_data should not have both a var dict and src/srcs set")
        srcs = var.values()
        var = ",".join(var.keys())
    elif src and srcs:
        fail("go_embed_data should not have both src and srcs set")
    elif src:
        srcs = [src]
    else:
        more_args += " -map"
    if out == None:
        out = name + ".go"
    if flatten:
        more_args += " -flatten"
    if string:
        more_args += " -string"
    native.genrule(
        name = name,
        srcs = srcs,
        outs = [out],
        tools = ["//go/tools:gen_go_data"],
        cmd = (
            "$(location //go/tools:gen_go_data)" +
            " -package " + package +
            " -var " + var + more_args +
            " $(SRCS) > $@"
        ),
        testonly = testonly,
        visibility = visibility,
        compatible_with = compatible_with,
    )

"""Preprocess SAI programs with the registered C compiler and published P4 headers."""

load("@rules_cc//cc:action_names.bzl", "ACTION_NAMES")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain", "use_cc_toolchain")
load("@rules_cc//cc/common:cc_common.bzl", "cc_common")

def _preprocess_p4_impl(ctx):
    toolchain = find_cc_toolchain(ctx)
    features = cc_common.configure_features(ctx = ctx, cc_toolchain = toolchain)
    compiler = cc_common.get_tool_for_action(
        feature_configuration = features,
        action_name = ACTION_NAMES.c_compile,
    )
    args = ctx.actions.args()
    args.add_all(["-E", "-C", "-undef", "-nostdinc", "-x", "assembler-with-cpp"])
    args.add("-I" + ctx.file._v1model.dirname)
    args.add("-I.")
    if ctx.attr.define:
        args.add("-D" + ctx.attr.define)
    args.add(ctx.file.src)
    args.add("-o", ctx.outputs.out)
    ctx.actions.run(
        executable = compiler,
        arguments = [args],
        inputs = depset(
            [ctx.file.src, ctx.file._v1model],
            transitive = [dep[DefaultInfo].files for dep in ctx.attr.deps + [ctx.attr._p4include]],
        ),
        tools = toolchain.all_files,
        outputs = [ctx.outputs.out],
        mnemonic = "PreprocessSaiP4",
    )

preprocess_p4 = rule(
    implementation = _preprocess_p4_impl,
    attrs = {
        "src": attr.label(allow_single_file = [".p4"], mandatory = True),
        "deps": attr.label_list(allow_files = True),
        "define": attr.string(),
        "_p4include": attr.label(default = "@com_github_p4lang_p4c//:p4include"),
        "_v1model": attr.label(default = "@com_github_p4lang_p4c//p4include:v1model.p4", allow_single_file = True),
    },
    outputs = {"out": "%{name}.p4"},
    fragments = ["cpp"],
    toolchains = use_cc_toolchain(),
)

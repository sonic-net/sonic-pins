"""Module extension for dependencies not available in the Bazel Central Registry."""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _non_bcr_deps_impl(ctx):
    http_archive(
        name = "com_github_otg_models",
        url = "https://github.com/open-traffic-generator/models/archive/refs/tags/v0.12.5.zip",
        strip_prefix = "models-0.12.5",
        build_file = "@//:bazel/BUILD.otg-models.bazel",
        sha256 = "1a63e769f1d7f42c79bc1115babf54acbc44761849a77ac28f47a74567f10090",
    )

    http_archive(
        name = "sonic_swss_common",
        # Post-hiredis-fix, pre-cfg_schema.h (which requires autotools generation).
        url = "https://github.com/azure/sonic-swss-common/archive/dc055659b6a1.zip",
        strip_prefix = "sonic-swss-common-dc055659b6a113903ab2ba87946bfbc8c39e6571",
        build_file = "@//:bazel/BUILD.sonic-swss-common.bazel",
    )

non_bcr_deps = module_extension(
    implementation = _non_bcr_deps_impl,
)

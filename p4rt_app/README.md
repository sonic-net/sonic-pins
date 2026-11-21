# p4rt_app

This package implements the P4Runtime daemon (`p4rt`) and companion CLI tools
for SONiC using Bazel 8.5.1 (Bzlmod) and shared `libswsscommon`
(`@sonic_swss_common//:libswsscommon_shared`).

## Quick Start

```bash
# Build production runtime TAR, debug symbols TAR, and OCI metadata
bazel build //p4rt_app:p4rt_runtime //p4rt_app:p4rt_runtime.debug_symbols //p4rt_app:runtime_packages.json

# Verify packaging, ELF hardening, .build-id GDB lookup, and shared library linkage
bazel test //p4rt_app:runtime_package_test

# Run all P4RT tests
bazel test //p4rt_app/...
```

Legacy `pkg_deb` targets (`//p4rt_app:p4rt_deb` and `//p4rt_app:p4rt_dbg_deb`)
remain tagged `manual` and are excluded from default `//...` builds.

# P4RT Production Runtime TARs

`//p4rt_app:p4rt_runtime`, `//p4rt_app:p4rt_runtime.debug_symbols`, and
`//p4rt_app:runtime_packages.json` (aliased at `//:runtime_packages.json`) are
built natively with Bazel 8.5.1 (Bzlmod) using `@sonic_build_infra`
(`sonic_deploy_tar` + `runtime_packages`) and `@sonic_swss_common//:libswsscommon_shared`.

## Produced targets

- `//p4rt_app:p4rt_runtime` — stripped ELF production binaries installed under
  `usr/local/bin/` with canonical root ownership and timestamps:
  - `p4rt`
  - `p4rt_program_table`
  - `p4rt_read`
  - `p4rt_set_forwarding_pipeline`
  - `p4rt_write`
- `//p4rt_app:p4rt_runtime.debug_symbols` — detached `.debug` ELF files indexed
  under `./usr/lib/debug/.build-id/<prefix>/<suffix>.debug` paired by GNU
  Build-ID with every binary in `p4rt_runtime`.
- `//p4rt_app:runtime_packages.json` (and `//:runtime_packages.json`) — OCI /
  Debian dependency metadata derived from `p4rt_app/debian/{control,changelog,compat}`
  and transitive `@sonic_swss_common` / `@libnl3` runtime metadata.

## Verification

Build and test on Debian Trixie (`@sonic_build_infra//platforms:x86_64_trixie`):

```bash
bazel test //p4rt_app:runtime_package_test
```

`runtime_package_test` verifies canonical archive entries, ELF hardening
(PIE, RELRO, `BIND_NOW`, non-executable `GNU_STACK`, zero RPATH/RUNPATH),
`DT_NEEDED: libswsscommon.so.0` on `p4rt`, paired `.build-id` debug symbols
via isolated `gdb` lookups, CLI execution, and `runtime_packages.json` metadata.

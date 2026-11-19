# Production runtime and debug TARs

The existing Bazel 6.4.0 source graph builds P4RT and its four production command-line
utilities. The public `//p4rt_app:p4rt_runtime` and
`//p4rt_app:p4rt_runtime_debug` targets expose those programs directly to a future
`sonic-buildimage` OCI consumer. They produce uncompressed TARs; neither invokes
Debian packaging. The existing private/test bundle and Debian targets are unchanged.

| Runtime path | Matching debug path |
| --- | --- |
| `usr/local/bin/p4rt` | `usr/local/bin/p4rt.dwp` |
| `usr/local/bin/p4rt_program_table` | `usr/local/bin/p4rt_program_table.dwp` |
| `usr/local/bin/p4rt_read` | `usr/local/bin/p4rt_read.dwp` |
| `usr/local/bin/p4rt_set_forwarding_pipeline` | `usr/local/bin/p4rt_set_forwarding_pipeline.dwp` |
| `usr/local/bin/p4rt_write` | `usr/local/bin/p4rt_write.dwp` |

The route-measurement test executable stays in the existing test bundle. Runtime
files have mode `0755`, debug files have mode `0644`, and TAR ownership and timestamps
are fixed to zero. Each optimized runtime ELF keeps the split-DWARF skeleton needed
to find its matching DWP file. This follows the existing SONiC P4RT compiler profile:
`opt`, split DWARF and DWARF 4 (GNU dwp 2.44 cannot package GCC 14's DWARF 5 output).
The targets are tagged `manual` because the production profile must be selected
explicitly; ordinary wildcard builds retain their existing configuration.

Prepare Common's native SDK using the established
[buildimage SDK handoff](https://github.com/securely1g/sonic-buildimage/pull/36).
That adapter builds Common once with Bazel 8.5.1 and supplies its headers and shared
library to this Bazel 6 WORKSPACE. Then build on native AMD64 Debian Trixie:

```sh
bazel build --config=p4rt-runtime \
  --override_repository=sonic_swss_common=/absolute/path/to/common-sdk \
  //p4rt_app:p4rt_runtime //p4rt_app:p4rt_runtime_debug
```

The production CI pins the existing SDK adapter and Common source, audits both
configured graphs before executing them, builds the two TARs, and runs every
`tests(//p4rt_app/...)` target. The installed-package test checks the exact production
inventory, paths/modes, actual Common library loading, original CLI flags and
P4RT's argument-validation entry point. It also checks every binary in a fresh GDB
process: source/type lookup must fail without the DWP and pass with the matching
DWP. These are offline installed-artifact checks; switch hardware behavior remains
covered by the existing project's applicable tests, not claimed by this TAR test.

For local acceptance with a prepared SDK and the pinned buildimage checkout:

```sh
python3 ci/production_runtime.py \
  --buildimage /absolute/path/to/sonic-buildimage \
  --sdk /absolute/path/to/common-sdk \
  --output-base /absolute/path/to/p4rt-bazel-output \
  --output artifacts/p4rt --jobs 2
```

Add future production executables to `_PRODUCTION_BINARIES` beside their source
build and to the installed-contract table/test. Their matching DWP files are
selected from that same list. No generated BUILD file or separate compilation
recipe is needed.

## Package identity for OCI consumers

The two `*_contract_template` targets expose the package controls and installed
paths beside the production TARs. Runtime dependencies use the same maintained
list as the existing Debian declaration; these targets do not produce a DEB.
The installed-package test compares both templates with the actual five-program
and DWP inventories.

`ci/production_runtime.py` publishes `p4rt_runtime_contract.json` and
`p4rt_runtime_debug_contract.json` after validation. It binds each template to
the clean source checkout's full Git commit and actual TAR SHA-256. OCI consumers
must use these bound contracts and verify their revision and hashes against the
producer handoff. A raw template is not an accepted handoff.

The contracts retain the real Bazel 6 WORKSPACE owner and original target names.
They do not invent a Bzlmod module identity. An image using a newer Common must
prepare the SDK from its selected parent source graph and validate that exact
library/interface combination; the production CI's older pinned SDK alone does
not establish compatibility with a different image parent.

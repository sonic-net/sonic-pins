# fourward/ — Agent Guide

**Always work in a dedicated git worktree — never modify the main tree
directly.** Create one with:

```sh
git worktree add ../sonic-pins-<branch> -b <branch>
```

## Repository map

```
fourward/fourward_server.{h,cc}       RAII subprocess manager for 4ward servers.
fourward/fourward_switch.{h,cc}       thinkit::Switch backed by a FourwardServer.
fourward/fourward_oracle.{h,cc}       Output + trace prediction via InjectPackets RPC.
fourward/fake_gnmi_service.h          In-process fake gNMI for port discovery.
fourward/packet_bridge.{h,cc}         Emulates back-to-back links between two instances.
fourward/fourward_mirror_testbed.h    thinkit::MirrorTestbed (two 4ward + gNMI + bridge).
fourward/trace_conversion.{h,cc}      TraceTree → PacketTrace conversion.
fourward/BUILD.bazel                  All build targets.
fourward/README.md                    Architecture overview and component docs.
fourward/AGENTS.md                    This file.
```

Unit tests live alongside the source: `foo_test.cc` next to `foo.{h,cc}`.

## Build and test

```sh
bazel build //fourward/...
bazel test //fourward/...
```

## Test-driven development

**Write the test first.** The test is the spec — it defines the behavior
you want before you write the code. If you can't write a clear test, you
don't understand the problem yet. A failing test is the starting point for
every change, not an afterthought.

## Code conventions

1. **We strictly follow the [Google C++ Style Guide](https://google.github.io/styleguide/cppguide.html)**
   and the [Abseil Tips of the Week](https://abseil.io/tips/).

2. **Unit tests for every `.h`/`.cc` pair.** No exceptions. A test for
   `foo.{h,cc}` must be named `foo_<optional_middle_part>_test.cc`.

3. **Use status macros** in production code:
   - `ASSIGN_OR_RETURN` instead of `if (!x.ok()) return x.status();`
   - `RETURN_IF_ERROR` instead of `if (!status.ok()) return status;`

4. **Use test status macros** in tests:
   - `ASSERT_OK_AND_ASSIGN` instead of `ASSERT_TRUE(x.ok()); auto val = *x;`
   - `ASSERT_OK`, `EXPECT_OK` instead of `EXPECT_TRUE(status.ok());`

5. **Propagate errors via status.** `absl::Status` or `absl::StatusOr` for
   all fallible operations. Logging errors (`LOG(ERROR)`) is not an
   acceptable way to report failures.

6. **Exhaustive switch on proto oneofs.** Never use if/else chains to
   dispatch on proto oneof fields.

7. **Use `int` for loop variables**, per Google Style Guide. The
   `-Wno-sign-compare` flag in `.bazelrc` suppresses warnings when comparing
   `int` against `.size()`. Never use `unsigned` or `size_t` for loops.

8. **Never fail silently.** Prefer compile-time failures (exhaustive switch)
   over runtime checks. When runtime checks are needed, return an error
   status with a descriptive message.

9. **Prefer golden tests for proto-to-proto or text-output functions.** Golden
   tests are less brittle than substring assertions — when output format
   changes, you just `--update` the golden file instead of fixing N assertions.
   Use `cmd_diff_test` from `@gutil//gutil:diff_test.bzl` with a runner binary
   that prints input + output for each test case. See
   `trace_conversion_golden_test` for a good example: a runner binary
   (`trace_conversion_golden_test_runner.cc`) prints the input TraceTree and
   output PacketTrace for each case, and `cmd_diff_test` diffs against
   `trace_conversion_test.expected`. Update via:
   `bazel run //fourward:trace_conversion_golden_test -- --update`.

## Debugging

When a test crashes, **observe, don't guess**:

```sh
# Debug build with symbols:
bazel run -c dbg //path/to:test -- --gtest_filter="*FailingTest*"

# Run under GDB:
bazel run -c dbg //path/to:test --run_under=gdb -- --gtest_filter="*FailingTest*"
```

## Key design invariants

1. **4ward is a subprocess.** All communication happens over gRPC. The C++
   code in this directory never links against 4ward's Kotlin code — it only
   depends on proto definitions and gRPC stubs.

2. **The `dvaas` namespace.** All code in `fourward/` lives in `namespace
   dvaas`, not `namespace fourward`. The `fourward` namespace belongs to the
   4ward repo.

3. **The integration is opt-in.** When `P4Specification.fourward_config` is
   present, DVaaS uses 4ward. Otherwise, the existing BMv2 path works
   unchanged.

## Commit messages

Focus on *why* the change is being made. Don't restate what the diff shows.

## Pull requests

Open PRs in draft mode (`gh pr create --draft`). Rebase onto `fork/main`
before submitting. Keep descriptions concise — lead with the win.

## Before submitting a PR

- Run `bazel test //fourward/...`. Fix all failures.
- Add unit tests for new behavior.
- Check whether README.md needs updating.

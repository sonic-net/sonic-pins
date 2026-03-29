# fourward/ — Agent Guide

1. **We strictly follow the [Google C++ Style Guide](https://google.github.io/styleguide/cppguide.html).**
2. **We strictly write unit tests for each and every `.h`/`.cc` pair.**
3. **Use status macros** (`ASSIGN_OR_RETURN`, `RETURN_IF_ERROR`) in production code instead of manual `if (!status.ok())` checks.
4. **Use test status macros** (`ASSERT_OK_AND_ASSIGN`, `ASSERT_OK`, `EXPECT_OK`) in tests instead of manual status checks.
5. **Propagate errors programmatically** via `absl::Status` or `absl::StatusOr`. Logging errors (`LOG(ERROR)`) is not an acceptable way to report failures — always return a status.

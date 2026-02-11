# Copilot Instructions for sonic-pins

## Project Overview

sonic-pins (P4 Integrated Network Stack) provides infrastructure and libraries for testing and integrating P4-programmable switches with SONiC. It includes the P4RT (P4Runtime) application, PDPI (P4 Data Plane Interface) utilities, SAI-P4 mapping tools, and test frameworks for PINS-enabled switches. This repo bridges the gap between P4 programmability and SONiC's traditional network stack.

## Architecture

```
sonic-pins/
├── p4rt_app/            # P4Runtime application for SONiC
├── p4_pdpi/             # P4 Data Plane Interface — P4Info utilities
├── p4_symbolic/         # Symbolic execution tools for P4 programs
├── p4_fuzzer/           # P4 program fuzzing tools
├── sai_p4/              # SAI-to-P4 mapping definitions
│   └── instantiations/  # P4 program instantiations for different platforms
├── dvaas/               # Data-plane validation as a service
├── gutil/               # gRPC utility library
├── lib/                 # Shared libraries
├── thinkit/             # Test infrastructure abstraction layer
├── tests/               # Integration tests
├── bazel/               # Bazel build configuration
├── .github/             # GitHub configuration
└── CONTRIBUTING.md      # Contribution guidelines
```

### Key Concepts
- **P4Runtime (P4RT)**: gRPC-based API for programming P4-defined forwarding tables
- **PDPI**: Utilities for working with P4Info, converting between PI and PD representations
- **SAI-P4**: Mapping between SAI (Switch Abstraction Interface) and P4 tables/actions
- **ThinKit**: Abstraction layer for interacting with test switches

## Language & Style

- **Primary languages**: C++ (core libraries, p4rt_app), Python (tests)
- **Build system**: Bazel
- **C++ standard**: C++17
- **Indentation**: 2 spaces (Google C++ style guide)
- **Naming conventions** (Google style):
  - Classes: `PascalCase`
  - Functions: `PascalCase` (Google style)
  - Variables: `snake_case`
  - Constants: `kPascalCase`
  - File names: `snake_case.cc/.h`
  - Namespaces: `snake_case`
- **Proto files**: Follow Google protobuf style guide

## Build Instructions

```bash
# Install Bazel (see https://bazel.build/install)

# Build all targets
bazel build //...

# Build specific target
bazel build //p4rt_app:p4rt_app

# Build with specific config
bazel build --config=dbg //...
```

## Testing

```bash
# Run all tests
bazel test //...

# Run specific test
bazel test //p4_pdpi:pdpi_test

# Run with verbose output
bazel test //... --test_output=all

# Run integration tests
bazel test //tests/...
```

- Tests use **Google Test** (C++) and **pytest** (Python)
- Bazel manages test dependencies and execution
- Integration tests in `tests/` may require switch connectivity
- Unit tests are co-located with source code

## PR Guidelines

- **Commit format**: Descriptive commit messages
- **Signed-off-by**: REQUIRED (`git commit -s`)
- **CLA**: Sign Linux Foundation EasyCLA
- **CONTRIBUTING.md**: Follow the repo's `CONTRIBUTING.md` for detailed guidelines
- **Code review**: Required before merge
- **Bazel**: Ensure all Bazel targets build and tests pass
- **Style**: Follow Google C++ Style Guide

## Common Patterns

### P4RT Table Entry Programming
```cpp
// P4RT app receives P4Runtime WriteRequest
// Translates P4 table entries to SAI API calls
// Programs the switch via SAI
```

### PDPI Usage
```cpp
// Convert P4Info to PDPI IR (Intermediate Representation)
// Use IR for validation, translation, and manipulation
// Convert between PI (Protocol Independent) and PD (Protocol Dependent) formats
```

### SAI-P4 Mapping
```
// sai_p4/ defines how SAI objects map to P4 tables/actions
// P4 programs in instantiations/ are compiled for specific platforms
// Mapping enables P4-based forwarding on SAI-compatible ASICs
```

## Dependencies

- **Bazel**: Build system
- **Abseil (absl)**: Google's C++ utility library
- **gRPC/protobuf**: RPC framework and serialization
- **P4Runtime**: P4Runtime protobuf definitions
- **Google Test**: Testing framework
- **SAI**: Switch Abstraction Interface headers
- **sonic-swss-common**: SONiC database integration (for p4rt_app)

## Gotchas

- **Bazel build system**: This repo uses Bazel, not autotools/Make like most SONiC repos
- **Google style**: Uses 2-space indent and Google naming conventions, unlike other SONiC repos (4-space)
- **P4 compiler**: Some targets require a P4 compiler (p4c) — ensure it's installed
- **Platform-specific P4**: P4 programs in `sai_p4/instantiations/` are platform-specific
- **Proto versioning**: P4Runtime proto changes must maintain backwards compatibility
- **Test infrastructure**: Integration tests may need ThinKit configuration for switch access
- **Large dependencies**: Bazel will download many external dependencies on first build
- **Branch**: Default branch is `main` (not `master` like most SONiC repos)

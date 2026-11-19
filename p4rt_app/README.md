# SONiC P4RT App

The SONiC P4RT App is a gRPC service supporting the
[P4Runtime](https://github.com/p4lang/p4runtime) interface for switches running
the SONiC operating system. This project is intended to be build and used by
[sonic-buildimage](https://github.com/pins/sonic-buildimage/tree/pins/202012_20210206/src/sonic-p4rt)

This is not an officially supported Google product.

This code is still a work in progress.

## System Dependencies

Debian Buster is the officially supported platform for building SONiC P4RT.

*   C++17
*   Bazel 4.0.0 or higher
*   Boost
*   libhiredis
*   libnl-3

```bash
$ sudo apt-get install -y \
      build-essential \
      git \
      libtool \
      pkg-config \
      libboost-all-dev
      libhiredis-dev \
      libnl-3-dev \
      libnl-genl-3-dev \
      libnl-route-3-dev \
      libnl-nf-3-dev
```

## Building & Testing P4RT App

Installing Bazel:

```bash
$ BAZEL_VERSION=4.0.0
$ wget https://github.com/bazelbuild/bazel/releases/download/$BAZEL_VERSION/bazel-$BAZEL_VERSION-installer-linux-x86_64.sh
$ chmod +x bazel-$BAZEL_VERSION-installer-linux-x86_64.sh
$ sudo ./bazel-$BAZEL_VERSION-installer-linux-x86_64.sh
```

Building a standalone P4RT App:

```bash
$ bazel build //p4rt_app:p4rt
```

Running all unit & component tests:

```bash
$ bazel test //p4rt_app/...
```

## Production TARs on native AMD64/Trixie

`ci/production_runtime.py` uses the existing Bazel 6.4.0 production profile and
Common's declared SDK. Its default `--phase=all` builds the two public TARs and
runs every original P4RT test plus the installed runtime/DWP test. It does not
build Debian packages. `--bazel` selects the owner Bazel executable independently
of the SDK producer's Bazel 8.5.1 executable; the existing environment and caches
are retained.

Container consumers can separate build and validation:

```sh
python3 ci/production_runtime.py --phase=build --bazel=/path/to/bazelisk \
  --buildimage=/path/to/sonic-buildimage --sdk=/path/to/common-sdk \
  --output-base=/path/to/owner-output-base --output=/path/to/p4rt-artifacts
# Assemble the image using the sealed TARs and source-owned contracts.
python3 ci/production_runtime.py --phase=test --bazel=/path/to/bazelisk \
  --buildimage=/path/to/sonic-buildimage --sdk=/path/to/common-sdk \
  --output-base=/path/to/owner-output-base --output=/path/to/p4rt-artifacts \
  --runtime-receipt=/path/to/prepared-runtime.json
```

The separate test phase requires the exact clean source, SDK headers/library,
TARs and sealed contracts recorded by the build phase. It also verifies the
prepared runtime's library hashes and actual Common resolution through the
declared ELF interpreter before and after running tests without cached results.
The 57 ELF tests reuse Common's exact runtime runner and private ELF copies.
The original golden shell test keeps its filters and comparison, and delegates
only its ELF child to that runner. The installed-package Python test keeps
native Python/GDB and invokes its P4RT CLIs through the same selected loader.
The production TARs remain unchanged.
The image's
preparation step supplies this runtime from its selected Common graph; the owner
driver does not install system libraries. A native host caller must provide the
matching prepared runtime rather than rely on ambient Common dependencies.

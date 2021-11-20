# SONiC P4RT App

The SONiC P4RT App is a gRPC service supporting the
[P4Runtime](https://github.com/p4lang/p4runtime) interface for switches running
the SONiC operating system. This project is intended to be built and used by
[sonic-buildimage](https://github.com/Azure/sonic-buildimage)

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

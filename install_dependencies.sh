#!/bin/bash
# Copyright 2021 Google LLC
#
# System dependencies required by sonic_swss_common, which is not yet a hermetic
# Bazel build. These are NOT built by Bazel and must be installed on the host.
#
# pins-infra strives for a hermetic build. Before adding a new system dependency,
# consider building it with Bazel or finding a Bzlmod module in the BCR.

# TODO: Avoid these system deps, ideally by making sonic_swss_common hermetic.
sudo apt-get update
sudo apt-get install \
  libhiredis-dev \
  libnl-3-dev \
  libnl-genl-3-dev \
  libnl-route-3-dev \
  libnl-nf-3-dev \
  libboost-dev \
  libboost-serialization-dev \
  libzmq3-dev \
  nlohmann-json3-dev \
  uuid-dev

#!/bin/bash

# Runs a set of tests that we have found often discover issues with the P4
# program. This should be run after update_p4program_derived_files.sh.

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
cd $DIR

# Abort on first error.
set -e

# To speed things up, we first build everything in parallel before testing
# things sequentially. Generated files should already be updated.
bazel build '...'

# Check P4 program.
bazel test :sai_p4info_test

# Check all pins_infra tests.
bazel test //third_party/pins_infra/...

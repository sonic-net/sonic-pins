#!/bin/bash

# Checks that the P4 program has been updated correctly by running all P4
# program tests and updating all files that are directly derived from the P4
# program such as P4Infos or PD protos.

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
cd $DIR

# To speed things up, we first build everything in parallel before testing
# things sequentially. Some failures here are expected, since generated files
# may need updating first.
bazel build '...'

# Abort on first error.
set -e

# Update the individual p4info files. Exclude special files that are covered
# after this loop.
bazel query :all \
  | grep '_up_to_date_test$' \
  | grep -vE ':(sai_pd|union_p4info)' \
  | while read target; do
    bazel run "${target}" -- --update
done

# union_p4info combines all the other p4info files.
bazel run :union_p4info_up_to_date_test -- --update

# Check P4 program.
bazel test :sai_p4info_test

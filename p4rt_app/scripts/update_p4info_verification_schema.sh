#!/bin/bash

readonly BASE_PATH="$(pwd)"
readonly PINS_INFRA="${BASE_PATH%%/pins_infra*}/pins_infra"
readonly P4INFO_FILE="${PINS_INFRA}/sai_p4/instantiations/google/unioned_p4info.pb.txt"
readonly P4RT_APP="${PINS_INFRA}/p4rt_app"
readonly SCHEMA_FILE="${P4RT_APP}/p4runtime/p4info_verification_schema.pb.txt"

cd ${PINS_INFRA}
bazel run "//p4rt_app/scripts:build_schema_from_p4info" \
  -- --p4info="${P4INFO_FILE}" --output="${SCHEMA_FILE}"

#ifndef SAI_HASHING_P4_
#define SAI_HASHING_P4_

#include <v1model.p4>
#include "../../fixed/headers.p4"
#include "../../fixed/metadata.p4"
#include "../../fixed/ids.h"
#include "../../fixed/minimum_guaranteed_sizes.p4"

#define ECMP_HASH_SEED 0
#define ECMP_HASH_OFFSET 0

#define LAG_HASH_SEED 0
#define LAG_HASH_OFFSET 0

control hashing(in headers_t headers,
                inout local_metadata_t local_metadata,
                in standard_metadata_t standard_metadata) {
  bit<32> seed = 0;
  bit<4> offset = 0;

  // TODO: need to set these values differently for S2 and S3
  // S2 is SAI_HASH_ALGORITHM_CRC_CCITT with offset 4
  // S3 is SAI_HASH_ALGORITHM_CRC       with offset 8
  @sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)
  @sai_hash_seed(ECMP_HASH_SEED)
  @sai_hash_offset(ECMP_HASH_OFFSET)
  @id(SELECT_ECMP_HASH_ALGORITHM_ACTION_ID)
  action select_ecmp_hash_algorithm() {
    // TODO:
    // this action should set a local `hash_algorithm` variable to the hash
    // algorithm, e.g. `HashAlgorithm.crc32`, which would then be used by
    // `compute_ecmp_hash_ipv4` and `compute_ecmp_hash_ipv6`. However, BMv2 does
    // not support variables of Enum types at this point. BMv2 generates this
    // error:
    //
    //     type not yet handled on this target
    //
    //     enum HashAlgorithm {
    //          ^^^^^^^^^^^^^
    seed = ECMP_HASH_SEED;
    offset = ECMP_HASH_OFFSET;
  }

  @sai_ecmp_hash(SAI_SWITCH_ATTR_ECMP_HASH_IPV4)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV4)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV4)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)
  @id(COMPUTE_ECMP_HASH_IPV4_ACTION_ID)
  action compute_ecmp_hash_ipv4() {
    hash(local_metadata.wcmp_selector_input,
         HashAlgorithm.crc32, /*base=*/1w0, {
         seed, headers.ipv4.src_addr, headers.ipv4.dst_addr,
         local_metadata.l4_src_port, local_metadata.l4_dst_port},
         /*max=2^16=*/17w0x10000);

     // Rotate the wcmp_selector_input by offset bits to the right.
     local_metadata.wcmp_selector_input =
         local_metadata.wcmp_selector_input >> offset |
         local_metadata.wcmp_selector_input << (WCMP_SELECTOR_INPUT_BITWIDTH - offset);
  }

  @sai_ecmp_hash(SAI_SWITCH_ATTR_ECMP_HASH_IPV6)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV6)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV6)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_IPV6_FLOW_LABEL)
  @id(COMPUTE_ECMP_HASH_IPV6_ACTION_ID)
  action compute_ecmp_hash_ipv6() {
    hash(local_metadata.wcmp_selector_input,
         HashAlgorithm.crc32, /*base=*/1w0, {
         seed, headers.ipv6.flow_label,
         headers.ipv6.src_addr, headers.ipv6.dst_addr,
         local_metadata.l4_src_port, local_metadata.l4_dst_port},
         /*max=2^16=*/17w0x10000);

     // Rotate the wcmp_selector_input by offset bits to the right.
     local_metadata.wcmp_selector_input =
         local_metadata.wcmp_selector_input >> offset |
         local_metadata.wcmp_selector_input << (WCMP_SELECTOR_INPUT_BITWIDTH - offset);
  }

  apply {
    select_ecmp_hash_algorithm();
    if (headers.ipv4.isValid()) {
      compute_ecmp_hash_ipv4();
    } else if (headers.ipv6.isValid()) {
      compute_ecmp_hash_ipv6();
    }
  }
}  // control hashing

// Today, LAGs are not fully modeled in the P4 program. They are created and
// managed outside the P4 program and the P4RT App. However, hashing
// configurations are very similar to ECMP which is why we DO model that config
// here.
control lag_hashing_config(in headers_t headers) {
  bit<32> lag_seed = 0;
  bit<4> lag_offset = 0;

  @sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)
  @sai_hash_seed(LAG_HASH_SEED)
  @sai_hash_offset(LAG_HASH_OFFSET)
  action select_lag_hash_algorithm() {
    // TODO: Model enums in BMv2.
    lag_seed = LAG_HASH_SEED;
    lag_offset = LAG_HASH_OFFSET;
  }

  @sai_lag_hash(SAI_SWITCH_ATTR_LAG_HASH_IPV4)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV4)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV4)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)
  @id(COMPUTE_LAG_HASH_IPV4_ACTION_ID)
  action compute_lag_hash_ipv4() {
    // TODO: Model LAG hashing in P4.
  }

  @sai_lag_hash(SAI_SWITCH_ATTR_LAG_HASH_IPV6)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV6)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV6)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)
  @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_IPV6_FLOW_LABEL)
  @id(COMPUTE_LAG_HASH_IPV6_ACTION_ID)
  action compute_lag_hash_ipv6() {
    // TODO: Model LAG hashing in P4.
  }

  apply {
    select_lag_hash_algorithm();
    if (headers.ipv4.isValid()) {
      compute_lag_hash_ipv4();
    } else if (headers.ipv6.isValid()) {
      compute_lag_hash_ipv6();
    }
  }
}  // control lag_hashing_config

#endif  // SAI_HASHING_P4_

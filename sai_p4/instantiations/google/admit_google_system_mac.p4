#ifndef SAI_ADMIT_GOOGLE_SYSTEM_MAC_P4_
#define SAI_ADMIT_GOOGLE_SYSTEM_MAC_P4_

// The System MAC is installed by the inband manager running locally on the
// switch. It is needed to allow simple communication with a controller before
// the P4Info is pushed.
control admit_google_system_mac(in headers_t headers,
                                inout local_metadata_t local_metadata) {
  apply {
     local_metadata.admit_to_l3 =
      (headers.ethernet.dst_addr == 0x00_1a_11_17_5f_80);
  }
}  // control system_mac_admit

#endif  // SAI_ADMIT_GOOGLE_SYSTEM_MAC_P4_

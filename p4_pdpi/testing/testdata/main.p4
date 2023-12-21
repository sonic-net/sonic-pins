#include <core.p4>
#include <v1model.p4>

@p4runtime_translation("", string)
type bit<12> string_id_t;

// HEX_STRING
type bit<10> normal_id_t;

// HEX_STRING
typedef bit<16> multicast_group_id_t;
typedef bit<16> replica_instance_t;

enum MeterColor_t { GREEN, YELLOW, RED };

// Note: no format annotations, since these don't affect anything
struct metadata {
  bit<1> val;
  normal_id_t normal;
  bit<10> field10bit;
  bit<32> ipv4;
  bit<128> ipv6;
  bit<48> mac;
  string_id_t str;
  string_id_t str2;
  MeterColor_t color;
  multicast_group_id_t multicast_group_id;
  string_id_t replica_port;
  replica_instance_t replica_instance;
}
struct headers {
}

@controller_header("packet_in")
header packet_in_header_t {
  // The port the packet ingressed on.
  @id(1)
  bit<10> ingress_port;
  // The initial intended egress port decided for the packet by the pipeline.
  @id(2)
  string_id_t target_egress_port;
  // Unused padding to test @padding annotation.
  @id(3)
  @padding
  bit<3> unused_padding;
}

@controller_header("packet_out")
header packet_out_header_t {
  // The port this packet should egress out of.
  @id(1)
  string_id_t egress_port;
  // Should the packet be submitted to the ingress pipeline instead of being
  // sent directly?
  @id(2)
  bit<1> submit_to_ingress;
  // Unused padding to test @padding annotation.
  @id(3)
  @padding
  bit<6> unused_padding;
}

// Note: proto_tag annotations are only necessary until PD supports the @id annotation, which will be preferred.

// Action with argument IDs changed
@id(1)
action do_thing_1(@id(2) bit<32> arg1, @id(1) bit<32> arg2) {
}

// Action with different argument types
@id(2)
action do_thing_2(@id(1) bit<10> normal,
               @id(2) @format(IPV4_ADDRESS) bit<32> ipv4,
               @id(3) @format(IPV6_ADDRESS) bit<128> ipv6,
               @id(4) @format(MAC_ADDRESS) bit<48> mac,
               @id(5) string_id_t str) {
}

// Generic action
@id(3)
action do_thing_3(@id(1) bit<32> arg1, @id(2) bit<32> arg2) {
}

@id(5)
action do_thing_4() {
}

@id(7) @unsupported
action unsupported_action(@refers_to(exact_table, normal) @id(1) bit<10> normal) 
{}


control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {

  bit<10> wcmp_selector_input = 0;

  // Table with field match ID annotations
  @id(1)
  table id_test_table {
    key = {
      meta.ipv4 : exact @id(2) @format(IPV4_ADDRESS) @name("ipv4");
      meta.ipv6 : exact @id(1) @format(IPV6_ADDRESS) @name("ipv6");
    }
    actions = {
      @proto_id(2) do_thing_1;
      @proto_id(1) do_thing_2;
      @defaultonly NoAction();
    }
    const default_action = NoAction();
  }

  // Table with exact matches
  @id(2)
  table exact_table {
    key = {
      meta.normal : exact @id(1) @name("normal");
      meta.ipv4 : exact @id(2) @format(IPV4_ADDRESS) @name("ipv4");
      meta.ipv6 : exact @id(3) @format(IPV6_ADDRESS) @name("ipv6");
      meta.mac : exact @id(4) @format(MAC_ADDRESS) @name("mac");
      meta.str : exact @id(5) @name("str");
    }
    actions = {
      @proto_id(1) NoAction();
    }
    const default_action = NoAction();
  }

  // Table with ternary matches
  @id(3)
  table ternary_table {
    key = {
      meta.normal : ternary @id(1) @name("normal");
      meta.ipv4 : ternary @id(2) @format(IPV4_ADDRESS) @name("ipv4");
      meta.ipv6 : ternary @id(3) @format(IPV6_ADDRESS) @name("ipv6");
      meta.ipv6[127:64] :
          ternary @id(6) @format(IPV6_ADDRESS) @name("ipv6_upper_64_bits");
      meta.ipv6[127:65] :
          ternary @id(7) @format(IPV6_ADDRESS) @name("ipv6_upper_63_bits");
      meta.mac : ternary @id(4) @format(MAC_ADDRESS) @name("mac");
      meta.val : ternary @id(5) @name("unsupported_field") @unsupported;
    }
    actions = {
      @proto_id(1) do_thing_3;
      @proto_id(2) unsupported_action;
      @defaultonly NoAction();
    }
    const default_action = NoAction();
  }

  // Table with lpm matches
  @id(4)
  table lpm1_table {
    key = {
      meta.ipv4 : lpm @id(1) @format(IPV4_ADDRESS) @name("ipv4");
    }
    actions = {
      @proto_id(1) NoAction();
    }
    const default_action = NoAction();
  }

  // Table with lpm matches
  @id(5)
  table lpm2_table {
    key = {
      meta.ipv6 : lpm @id(1) @format(IPV6_ADDRESS) @name("ipv6");
    }
    actions = {
      @proto_id(1) NoAction();
    }
    const default_action = NoAction();
  }

  action_selector(HashAlgorithm.identity, 1024, 10) wcmp_group_selector;

  // WCMP table
  @id(6)
  @oneshot()
  @weight_proto_id(1)
  table wcmp_table {
    key = {
      meta.ipv4 : lpm @id(1) @format(IPV4_ADDRESS) @name("ipv4");
      wcmp_selector_input : selector;
    }
    actions = {
      @proto_id(2) do_thing_1;
    }
    implementation = wcmp_group_selector;
  }

  @id(3)
  direct_meter<MeterColor_t>(MeterType.bytes) my_meter;

  @id(2)
  direct_counter(CounterType.packets_and_bytes) my_counter;

  // Generic action
  @id(4)
  @name("count_and_meter")
  action count_and_meter() {
    my_meter.read(meta.color);
    my_counter.count();
  }

  // metered and counted table
  @id(7)
  @weight_proto_id(1)
  table count_and_meter_table {
    key = {
      meta.ipv4 : lpm @id(1) @format(IPV4_ADDRESS) @name("ipv4");
    }
    actions = {
      @proto_id(1) count_and_meter;
      @defaultonly NoAction();
    }
    meters = my_meter;
    counters = my_counter;
    const default_action = NoAction();
  }

  // WCMP table with multiple actions
  @id(8)
  @oneshot()
  @weight_proto_id(1)
  table wcmp2_table {
    key = {
        meta.ipv4 : lpm @id(1) @format(IPV4_ADDRESS) @name("ipv4");
        wcmp_selector_input : selector;
    }
    actions = {
      @proto_id(2) do_thing_1;
      @proto_id(3) do_thing_2;
    }
    implementation = wcmp_group_selector;
  }

  // Table with optional matches
  @id(9)
  table optional_table {
    key = {
      meta.ipv4 : optional @id(2) @format(IPV4_ADDRESS) @name("ipv4");
      meta.ipv6 : optional @id(1) @format(IPV6_ADDRESS) @name("ipv6");
      meta.str : optional @id(3) @name("str");
      #ifdef PDPI_EXTRA_MATCH_FIELD
      meta.mac : optional @id(4) @name("mac");
      #endif
      }
    actions = {
      @proto_id(1) do_thing_1;
      @defaultonly NoAction();
    }
    const default_action = NoAction();
  }


  table two_match_fields_table {
    key = {
        meta.str : exact @id(1) @name("id_1");
        meta.normal : exact @id(2) @name("id_2");
    }
    actions = {
      @proto_id(1) do_thing_4;
      @proto_id(2) do_thing_1;
      @defaultonly NoAction();
    }
    const default_action = NoAction();
  }

  table one_match_field_table {
    key = {
      meta.str : exact @id(1) @name("id");
    }
    actions = {
      @proto_id(1) do_thing_4;
      @defaultonly NoAction();
    }
    const default_action = NoAction();
  }

  // Action that refers to both fields of two_match_fields_table.
  // TODO Add double reference.
  action referring_to_two_match_fields_action(@id(1)
  @refers_to(two_match_fields_table, id_1)
                         string_id_t referring_id_1,
                         @id(2) @refers_to(two_match_fields_table, id_2)
                          normal_id_t referring_id_2) {}

  action referring_to_one_match_field_action(@id(1)
  @refers_to(one_match_field_table, id)
  // TODO: b/263309221 - Uncomment once multiple references are supported.
  // @refers_to(two_match_fields_table, id_1)
                         string_id_t referring_id_1) {}
  // A table whose entries refer to other table entries via action.
  table referring_by_action_table {
    key = {
      meta.normal : exact @id(1) @name("val");
    }
    actions = {
      @proto_id(1) referring_to_two_match_fields_action;
      @proto_id(2) referring_to_one_match_field_action;
      @defaultonly NoAction();
    }
    const default_action = NoAction();
  }

  // A table whose entries refer to other table entries via their own
  // match fields.
  table referring_by_match_field_table {
    key = {
      meta.str : exact @id(1) @name("referring_id_1")
      @refers_to(two_match_fields_table, id_1);
      meta.normal : exact @id(2) @name("referring_id_2")
      @refers_to(two_match_fields_table, id_2);
    }
    actions = {
      @proto_id(1) do_thing_4;
      @defaultonly NoAction();
    }
    const default_action = NoAction();
  }

  // Table with no actions
  @id(13)
  table no_action_table {
    key = {
      meta.ipv4 : exact @id(2) @format(IPV4_ADDRESS) @name("ipv4");
      meta.ipv6 : exact @id(1) @format(IPV6_ADDRESS) @name("ipv6");
    }
    actions = {
    }
  }

  // Table that refers to referring_by_match_field_table.
  table referring_to_referring_by_match_field_table {
      key = {
          meta.str : exact @id(1) @name("referring_to_referring_id_1")
          @refers_to(referring_by_match_field_table, referring_id_1);
      }
      actions = {
        @proto_id(1) do_thing_4;
        @defaultonly NoAction();
      }
      const default_action = NoAction();
  }

  // Unsupported table
  @id(15) @unsupported
  table unsupported_table {
      key = {
        meta.ipv4 : exact @id(2) @format(IPV4_ADDRESS) @name("ipv4");
        meta.ipv6 : exact @id(1) @format(IPV6_ADDRESS) @name("ipv6");
        meta.mac : exact @id(3) @format(MAC_ADDRESS) @name("mac")
          @refers_to(exact_table, mac);
      }
      actions = {
        @defaultonly NoAction();
      }
      const default_action = NoAction();
  }

  // Packet only counter
  @id(16)
  direct_counter(CounterType.packets) my_packets_counter;

  @id(17)
  direct_meter<MeterColor_t>(MeterType.bytes) my_meter2;

  // Packet only count action
  @id(18)
  @name("packet_count_and_meter")
  action packet_count_and_meter() {
    my_meter2.read(meta.color);
    my_packets_counter.count();
  }

  // metered and packet only counted table
  @id(19)
  @weight_proto_id(1)
  table packet_count_and_meter_table {
    key = {
      meta.ipv4 : lpm @id(1) @format(IPV4_ADDRESS) @name("ipv4");
    }
    actions = {
      @proto_id(1) packet_count_and_meter;
      @defaultonly NoAction();
    }
    meters = my_meter2;
    counters = my_packets_counter;
    const default_action = NoAction();
  }

  // Bytes only counter
  @id(20)
  direct_counter(CounterType.bytes) my_bytes_counter;

  @id(21)
  direct_meter<MeterColor_t>(MeterType.bytes) my_meter3;

  // Bytes only count action
  @id(22)
  @name("byte_count_and_meter")
  action byte_count_and_meter() {
    my_meter3.read(meta.color);
    my_bytes_counter.count();
  }

  // metered and bytes only counted table
  @id(23)
  @weight_proto_id(1)
  table byte_count_and_meter_table {
    key = {
      meta.ipv4 : lpm @id(1) @format(IPV4_ADDRESS) @name("ipv4");
    }
    actions = {
      @proto_id(1) byte_count_and_meter;
      @defaultonly NoAction();
    }
    meters = my_meter3;
    counters = my_bytes_counter;
    const default_action = NoAction();
  }

  // Table with both exact and optional matches.
  table exact_and_optional_table {
    key = {
      meta.ipv4 : exact @id(2) @format(IPV4_ADDRESS) @name("ipv4");
      meta.ipv6 : exact @id(1) @format(IPV6_ADDRESS) @name("ipv6");
      meta.str : optional @id(3) @name("str");
    }
    actions = {
      @proto_id(1) do_thing_4;
      @defaultonly NoAction();
    }
    const default_action = NoAction();
    }

  // Table with constraints.
  @entry_restriction("
    // Exact constraint with OR.
    normal == 5 || normal == 6;
    // LPM constraint.
    ipv4::prefix_length != 0;
    // Ternary constraint with exact set.
    field10bit == 0xff;
    // Large integer (most significant bit position > 64).
    ipv6 == 0xffffffffffffffffffffffff;
    // Ternary constraint with value.
    mac::mask != 0 -> mac::value == 10;
    // Implies constraint.
    val == 1 -> mac::mask != 0;
    // Metadata constraint.
    ::priority > 500;
    // P4runtime translated string constraint without reference.
    // TODO: This constraint should read
    // `nonreferring_str != ''`, but p4-constraints does not currently
    // support strings.
    nonreferring_str != 0;
    // P4runtime translated string constraint with reference.
    // TODO: This constraint should read
    // `referring_str != 'some_str'` (or equals), but p4-constraints does not
    // currently support strings. The current constraint is redundant.
    referring_str::mask != 0 -> referring_str != 0;
  ")
  table constrained_table {
    key = {
      meta.val : optional @id(1) @name("val");
      meta.normal : exact @id(2) @name("normal");
      meta.field10bit : ternary @id(8) @name("field10bit");
      meta.ipv4 : lpm @id(3) @format(IPV4_ADDRESS) @name("ipv4");
      meta.ipv6 : ternary @id(4) @format(IPV6_ADDRESS) @name("ipv6");
      meta.mac : ternary @id(5) @format(MAC_ADDRESS) @name("mac");
      meta.str : optional @id(6) @name("referring_str");
      meta.str2 : optional @id(7) @name("nonreferring_str");
        }
      actions = {
        @proto_id(1) do_thing_4;
        @defaultonly NoAction();
      }
      const default_action = NoAction();
    }

  action refers_to_multicast_action(
    @id(1)
    @refers_to(builtin::multicast_group_table, multicast_group_id)
    multicast_group_id_t multicast_group_id) {}

  table refers_to_multicast_by_action_table {
    key = {
      meta.str : exact @id(1) @name("val");
    }
    actions = {
      @proto_id(1) refers_to_multicast_action;
      @defaultonly NoAction();
    }
        const default_action = NoAction();
  }

  table refers_to_multicast_by_match_field_table {
    key = {
      meta.multicast_group_id : exact
        @id(1)
        @name("group_id")
        @refers_to(builtin::multicast_group_table, multicast_group_id);
    }
    actions = {
      @proto_id(1) do_thing_4;
      @defaultonly NoAction();
    }
    const default_action = NoAction();
  }

  table referenced_by_multicast_replica_table {
    key = {
      meta.replica_port : exact
        @id(1)
        @name("port")
        @referenced_by(builtin::multicast_group_table, replica.port);
      meta.replica_instance : exact
        @id(2)
        @name("instance")
        @referenced_by(builtin::multicast_group_table, replica.instance);
    }
    actions = {
      @proto_id(1) do_thing_4;
      @defaultonly NoAction();
    }
    const default_action = NoAction();
  }

  // This action only contains args whose formats are STRING. Values with the
  // STRING format are unchanged when translated from PD to IR/PI making it
  // easy to read values in any representation when golden testing.
  action golden_test_friendly_action(
    @id(1)
    string_id_t arg1,
    @id(2)
    string_id_t arg2) {}

  // Same as `golden_test_friendly_action` but with a different name so
  // `golden_test_friendly_wcmp_table` can use 2 different actions.
  action other_golden_test_friendly_action(
    @id(1)
    string_id_t arg1,
    @id(2)
    string_id_t arg2) {}

  // This table only contains fields whose formats are STRING. Values with the
  // STRING format are unchanged when translated from PD to IR/PI making it
  // easy to read values in any representation when golden testing.
  table golden_test_friendly_table {
    key = {
      meta.str : exact
        @id(1)
        @name("key1");
      meta.str2 : exact
        @id(2)
        @name("key2");
    }
    actions = {
      @proto_id(1) golden_test_friendly_action;
    }
  }

  // This table is a wcmp version of `golden_test_friendly_table`.
  @oneshot()
  @weight_proto_id(1)
  table golden_test_friendly_wcmp_table {
    key = {
      meta.str : exact
        @id(1)
        @name("key1");
      meta.str2 : exact
        @id(2)
        @name("key2");
      wcmp_selector_input : selector;
    }
    actions = {
      @proto_id(1) golden_test_friendly_action;
      @proto_id(2) other_golden_test_friendly_action;
    }
    implementation = wcmp_group_selector;
  }

  apply {
    id_test_table.apply();
    exact_table.apply();
    ternary_table.apply();
    lpm1_table.apply();
    lpm2_table.apply();
    wcmp_table.apply();
    count_and_meter_table.apply();
    wcmp2_table.apply();
    optional_table.apply();
    two_match_fields_table.apply();
    one_match_field_table.apply();
    referring_by_action_table.apply();
    referring_by_match_field_table.apply();
    no_action_table.apply();
    referring_to_referring_by_match_field_table.apply();
    unsupported_table.apply();
    packet_count_and_meter_table.apply();
    byte_count_and_meter_table.apply();
    exact_and_optional_table.apply();
    constrained_table.apply();
    refers_to_multicast_by_action_table.apply();
    refers_to_multicast_by_match_field_table.apply();
    referenced_by_multicast_replica_table.apply();
    golden_test_friendly_table.apply();
    golden_test_friendly_wcmp_table.apply();
  }
}

// Boilerplate definitions that are required for v1model, but do not affect the
// P4Info file (and thus do not matter for PDPI).

parser packet_parser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
  state start {
    transition accept;
  }
}
control checksum_verify(inout headers hdr, inout metadata meta) {
  apply {}
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t tandard_metadata) {
  apply {}
}
control checksum_compute(inout headers hdr, inout metadata meta) {
  apply {}
}
control packet_deparser(packet_out packet, in headers hdr) {
  apply {}
}
V1Switch(
  packet_parser(),
  checksum_verify(),
  ingress(),
  egress(),
  checksum_compute(),
  packet_deparser()
) main;

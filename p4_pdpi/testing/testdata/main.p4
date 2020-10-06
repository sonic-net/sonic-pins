#include <core.p4>
#include <v1model.p4>

@p4runtime_translation("", string)
type bit<12> string_id_t;

enum MeterColor_t { GREEN, YELLOW, RED };

// Note: no format annotations, since these don't affect anything
struct metadata {
  bit<1> val;
  bit<10> normal;
  bit<32> ipv4;
  bit<128> ipv6;
  bit<48> mac;
  string_id_t str;
  MeterColor_t color;
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
      meta.mac : ternary @id(4) @format(MAC_ADDRESS) @name("mac");
    }
    actions = {
      @proto_id(1) do_thing_3;
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
      }
      actions = {
        @proto_id(1) do_thing_1;
        @defaultonly NoAction();
      }
      const default_action = NoAction();
  }

  // Table that refers to another table
  @id(10)
  table referred_table {
      key = {
          meta.str : exact @id(1) @name("id");
      }
      actions = {
        @proto_id(1) do_thing_4;
        @defaultonly NoAction();
      }
      const default_action = NoAction();
  }
  // Generic action
  @id(6)
  action referring_action(@id(1) @refers_to(referred_table, id)
                         string_id_t referring_id_1,
                         @id(2) @refers_to(referred_table, id)
                         string_id_t referring_id_2) {}
  @id(11)
  table referring_table {
      key = {
          meta.normal : exact @id(1) @name("val");
      }
      actions = {
        @proto_id(1) referring_action;
        @defaultonly NoAction();
      }
      const default_action = NoAction();
  }

  @id(12)
  table referring2_table {
      key = {
          meta.str : exact @id(1) @name("referring_id")
          @refers_to(referred_table, id);
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
    referred_table.apply();
    referring_table.apply();
    referring2_table.apply();
    no_action_table.apply();
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

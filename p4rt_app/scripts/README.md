# Using P4RT helper tools

## Building the P4RT helper tools

The P4RT tools can be built individually with Bazel. They can also be built as
part of the `p4rt_deb.deb` package:

```bash
$ bazel build //p4rt_app:p4rt_deb
```

Once copied into the sonic-p4rt container the debian package can be installed
using:

```bash
$ apt install --reinstall /etc/sonic/p4rt_deb.deb
```

## Useful Command Examples

Push a default MiddleBlock config to the switch:

```bash
$ /usr/local/bin/p4rt_set_forwarding_pipeline \
  --p4rt_device_id=$(redis-cli -n 4 hget "NODE_CFG|integrated_circuit0" "node-id") \
  --forwarding_action="RECONCILE_AND_COMMIT" --default_middleblock_p4info
```

Send a pdpi::IrWrite request to the switch. See Appendix A for sample files:

```bash
$ /usr/local/bin/p4rt_write \
  --p4rt_device_id=$(redis-cli -n 4 hget "NODE_CFG|integrated_circuit0" "node-id") \
  --ir_write_request_file=/etc/sonic/sample.pb.txt
```

Read back all the table entries as pdpi::IrTableEntry(s):

```bash
$ /usr/local/bin/p4rt_read \
  --p4rt_device_id=$(redis-cli -n 4 hget "NODE_CFG|integrated_circuit0" "node-id")
```

## Appendix A: Sample pdpi::IrWrite Requests

```
# Create a VRF called 'vrf-1'.
updates {
  type: INSERT
  table_entry {
    table_name: "vrf_table"
    matches { name: "vrf_id" exact { str: "vrf-1" } }
    action { name: "no_action" }
  }
}
```

```
# Allow traffic with dst_mac=00:00:CC:CC:00:00 to be L3 routed.
updates {
  type: INSERT
  table_entry {
    table_name: "l3_admit_table"
    priority: 1
    matches {
      name: "dst_mac"
      ternary { value { mac: "00:00:CC:CC:00:00" } mask { mac: "FF:FF:FF:FF:FF:FF"} }
    }
    action { name: "admit_to_l3" }
  }
}
```

```
# Create a WCMP route that forwards IPv6 traffic:
#   dst_ip=2002:a17:506:c114::
#   vrf=vrf-1
# out the port with ID=1.

# ===== Router Interface, Neighbor and NextHop =================
updates {
  type: INSERT
  table_entry {
    table_name: "router_interface_table"
    matches { name: "router_interface_id" exact { str: "rid-1" } }
    action {
      name: "set_port_and_src_mac"
      params { name: "port" value { str: "1" } }
      params { name: "src_mac" value { mac: "00:00:AA:AA:00:00" } }
    }
  }
}
updates {
  type: INSERT
  table_entry {
    table_name: "neighbor_table"
    matches { name: "router_interface_id" exact { str: "rid-1" } }
    matches { name: "neighbor_id" exact { ipv6: "fe80::21a:11ff:fe17:5f81" } }
    action {
      name: "set_dst_mac"
      params { name: "dst_mac" value { mac: "00:00:BB:BB:00:00" } }
    }
  }
}
updates {
  type: INSERT
  table_entry {
    table_name: "nexthop_table"
    matches { name: "nexthop_id" exact { str: "nexthop-1" } }
    action {
      name: "set_ip_nexthop"
      params { name: "router_interface_id" value { str: "rid-1" } }
      params { name: "neighbor_id" value { ipv6: "fe80::21a:11ff:fe17:5f81" } }
    }
  }
}
# ===== WCMP Group =============================================
updates {
  type: INSERT
  table_entry {
    table_name: "wcmp_group_table"
    matches { name: "wcmp_group_id" exact { str: "group-1" } }
    action_set {
      actions {
        action { name: "set_nexthop_id" params { name: "nexthop_id" value { str: "nexthop-1" }}}
        weight: 1
      }
    }
  }
}
# ===== IPv6 ===================================================
updates {
  type: INSERT
  table_entry {
    table_name: "ipv6_table"
    matches { name: "vrf_id" exact { str: "vrf-1" } }
    matches { name: "ipv6_dst" lpm { value { ipv6: "2002:a17:506:c114::" } prefix_length: 64 } }
    action {
      name: "set_wcmp_group_id"
      params { name: "wcmp_group_id" value { str: "group-1" } }
    }
  }
}
```

```
# ===== Assign all traffic to vrf-1 ============================
updates {
  type: INSERT
  table_entry {
    table_name: "acl_pre_ingress_table"
    priority: 2000
    action {
      name: "set_vrf"
      params { name: "vrf_id" value { str: "vrf-1" } }
    }
  }
}
```

```
# ===== Punt all traffic to the CPU ============================
updates {
  type: INSERT
  table_entry {
    table_name: "acl_ingress_table"
    priority: 2
    action {
      name: "acl_trap",
      params {
        name: "qos_queue"
        value { str: "0x1" }
      }
    }
  }
}
```

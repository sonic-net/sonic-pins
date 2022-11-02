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

```bash
# Push a default MiddleBlock config to the switch.
$ /usr/local/bin/p4rt_set_forwarding_pipeline --forwarding_action="RECONCILE_AND_COMMIT" --default_middleblock_p4info
```

```bash
# Send a pdpi::IrWrite request to the switch. See Appendix A for sample files.
$ /usr/local/bin/p4rt_write --ir_write_request_file=/etc/sonic/sample.pb.txt
```

```bash
# Read back all the table entries as pdpi::IrTableEntry(s)
$ /usr/local/bin/p4rt_read
```

## Appendix A: Sample pdpi::IrWrite Requests

```
# Router Interface entry:
updates {
  type: INSERT
  table_entry {
    table_name: "router_interface_table"
      matches {
      name: "router_interface_id"
      exact { str: "rid-1" }
    }
    action {
      name: "set_port_and_src_mac"
      params {
        name: "port"
        value { str: "1" }
      }
      params {
        name: "src_mac"
        value { mac: "00:00:AA:AA:00:00" }
      }
    }
  }
}
```

```
# Neighbor entry:
updates {
  type: INSERT
  table_entry {
    table_name: "neighbor_table"
    matches {
      name: "router_interface_id"
      exact { str: "rid-1" }
    }
    matches {
      name: "neighbor_id"
      exact { str: "neighbor-1" }
    }
    action {
      name: "set_dst_mac"
      params {
        name: "dst_mac"
        value { mac: "00:00:BB:BB:00:00" }
      }
    }
  }
}
```

```
# Nexthop entry:
updates {
  type: INSERT
  table_entry {
    table_name: "nexthop_table"
    matches {
      name: "nexthop_id"
      exact { str: "nexthop-1" }
    }
    action {
      name: "set_ip_nexthop"
      params {
        name: "router_interface_id"
        value { str: "rid-1" }
      }
      params {
        name: "neighbor_id"
        value { str: "neighbor-1" }
      }
    }
  }
}
```

```
# ACL Ingress entry:
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

# Basic IPv4 forwarding

This is a simple P4 program that implements basic IPv4 forwarding.

Taken from https://github.com/p4lang/tutorials basic tutorial.

It performs the following pipeline on every received packet: * parse the packet
and extract the ethernet and ipv4 headers * lookup the mac address and out going
port of the next hop from the control plane tables * update packet headers with
the new address and port and decrement ttl * serialize (deparse) packet and send
it via the new port

## Test Architecture

The test follows a very simple network architecture.

The switch is connected to two ports: 0 and 1, with 4 virtual ethernet
interfaces: veth0, veth1, veth2, and veth3.

veth0 and veth1 are piped togther, same with veth2 and veth3. Packets sent via
veth0 appear as outputs on veth1 and vice-versa.

Finally, the switch assigns veth0 to port 0, and veth1 to port 1.

The control plane has two longest prefix rules: it routes all packets to
10.10.0.0/16 to port 0 (thus they appear at veth1) and all packets to
20.20.0.0/16 to port 1 (thus they appear at veth3). Other packets are dropped.

The makefile sends 4 test packets: two to 20.20.0.*, and one to 10.10.0.*, using
differnet ports. The makefile monitors packets through veth3 (the other end of
port 1), and thus shows exactly three of these packets: 2 forwarded from the
switch, and one input packet into the switch.

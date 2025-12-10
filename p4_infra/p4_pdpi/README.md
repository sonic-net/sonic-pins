![build](https://github.com/google/p4-pdpi/workflows/build/badge.svg)
![test](https://github.com/google/p4-pdpi/workflows/test/badge.svg)

# P4 PDPI

P4Runtime generally uses a program-independent representation (or PI) for P4
entities such as table entries, counters, etc. This is achieved by using numeric
IDs instead of names. The downside of this is that the representation is hard to
read by humans. In contrast, a program-dependent (or PD) representation uses
names and is generally more friendly to humans.

This repository provides several PD-like representations, and code to
automatically convert between them.

This is a work in progress.

This is not an officially supported Google product.


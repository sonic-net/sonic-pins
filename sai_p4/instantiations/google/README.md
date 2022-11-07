# Google P4 Programs

Note: After any update to p4 files, run `update_p4program_derived_files.sh` to
update the derived protobufs.

## Directory Overview

This directory contains google-specific P4 programs, their derived P4Info
protobufs, and C++ libraries to pull them.

The main interface for this directory is `sai_p4info.h`, which will return the
default P4Info protobuf for each instantiation.

A more advanced library, `sai_p4info_builder.h`, can be used for pulling P4Info
files with more advanced differences.

## Top-Level P4 Programs

The table below lists all the top-level P4 programs. P4 files (\*.p4) not listed
contain P4 components or definitions that are used by the top-level P4 programs.

All top-level P4 programs listed below have an accompanying P4Info text proto.
I.e. for each row, the following files exist:

*   P4 Program: \<name\>.p4
*   Derived P4Info protobuf: \<name\>.p4info.pb.txt

| P4 Program                           | Description                           |
| ------------------------------------ | ------------------------------------- |
| middleblock                          | Preferred P4 program for middleblock  |
:                                      : switches.                             :
| fabric\_border\_router               | P4 program for fabric border router   |
:                                      : switches.                             :
| wbb                                  | P4 program for WAN Building Block     |
:                                      : switches.                             :
| middleblock\_with\_s2\_ecmp\_profile | Equivalent to **middleblock** in most |
:                                      : cases. Includes hashing annotations   :
:                                      : particular to Stage 2 switches.       :
| middleblock\_with\_s3\_ecmp\_profile | Equivalent to **middleblock** in most |
:                                      : cases. Includes hashing annotations   :
:                                      : particular to Stage 3 switches.       :

**middleblock**, **fabric_border_router**, and **wbb** programs are provided
through `sai_p4info.h` as separate *Instantiations*.

**middleblock_with_s2_ecmp_profile** and **middleblock_with_32_ecmp_profile**
can only be accessed from `sai_p4info_builder.h`. These programs are identitcal
to **middleblock** with the exception of ECMP hashing annotations.

NOTE: None of the P4 programs in this directory correctly model hashing
behavior.

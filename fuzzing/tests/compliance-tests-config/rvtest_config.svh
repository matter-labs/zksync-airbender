// rvtest_config.svh
// SPDX-License-Identifier: Apache-2.0

// This file is needed in the config subdirectory for each config supporting coverage.
// It defines which extensions are enabled for that config.

`define XLEN 32

// PMP Grain (G) is 0 for this target.
`define G_IS_0

// Base addresses specific for PMP
`define RAM_BASE_ADDR       32'h00000000  // PMP Region starts at RAM_BASE_ADDR + LARGEST_PROGRAM
`define LARGEST_PROGRAM     32'h00040000

// Define relevant addresses
`define ACCESS_FAULT_ADDRESS 64'h00000000
`define CLINT_BASE 64'h02000000

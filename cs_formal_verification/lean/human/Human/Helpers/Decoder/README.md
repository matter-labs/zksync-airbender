# Public decoding and instruction selection

This directory relates public instruction bytes and our RV32 decoder (`RV.decode`) to
native family, register, immediate and selector metadata. The ROM image of the public
`RV.State` holds the program; fetch reads it and no history step changes it. Decoder-table
membership is a logical connection between the public program and witness rows, with
preprocessing provenance reviewed separately.

## Checked connections

Successful public-program construction (`rvProgramImageWith`) implies that each entry is an
aligned ROM word read by `RV.read` from the starting ROM image, decoded by `RV.decode`, and
projected to native metadata; see
[`rvProgramEntryWith_some`](../../../../slop/Slop/Trace/RVFetch.lean) (the guard, the public bytes, the decoded
instruction and its metadata). Decoder-table membership of a witness row yields a program entry of that family with the
row's query ([`rv_decoder_member`](../../../../slop/Slop/Trace/RVProgram.lean)). The table's fetch guard
(`rvProgramEntryWith`) places every entry's PC in ROM and 4-byte aligned, so no code-domain or
alignment premise is needed.

With logical decoder membership, the instruction used by retirement is `RV.decode` of the
entry's bytes at the current PC; see [rv_execution_soundness](../../Trace/UnifiedReduced/RVTheorems.lean) and
[rv_pooled_native_soundness](../../Trace/RVSoundness.lean). Actual source decoding is
proved; correspondence with Rust preprocessing/setup is still a separate condition.
`RV.decode` itself is tied to Sail's decoder by `DecodeIsSailClaim` in the
[equivalence leaf](../../ISA/Sail/Theorems.lean).

Start with [RVProgram](RVProgram.lean): public bytes are read, decoded by `RV.decode` and
projected into native family/register/immediate metadata. The public entry record alone does not
establish correct decoding. [Program](Program.lean) holds the shared native metadata types.
`RVDecoded` (in [the ADD/SUB and word-memory trace claim](../../Trace/Families/AddSub/RVTheorems.lean))
states decoder-table membership for the restricted scope.

[Columns](Columns.lean) identifies imported decoder columns.
[RVPooledProgram](RVPooledProgram.lean) combines the six admitted families and defines
logical decoder-table membership (`RVPooledDecoded`). Family projections remain in their
circuit directories (`Circuits/*/RVDecoder.lean`). `RVCycleFetch` in
[RVCallerCycles](../../Trace/UnifiedReduced/RVCallerCycles.lean) binds fetch to the current history state.

[ExternalInput](ExternalInput.lean), [RVExternalInput](RVExternalInput.lean) and
[PooledExternalInput](PooledExternalInput.lean) add the CSR 0x7C0 read/write forms (the only
CSR forms besides delegation calls that have a next state) and their independent-stream connection.

Check source bytes, full metadata and selector membership. Desired decoder answers are not
independent premises. Rust preprocessing and modeled-table provenance remain trust
boundaries; these definitions do not prove an extracted setup generator or cryptographic
lookup argument.

Public initialization is in [Context](../Context/README.md); byte interpretation
and preserved history are in [Memory](../Memory/README.md).

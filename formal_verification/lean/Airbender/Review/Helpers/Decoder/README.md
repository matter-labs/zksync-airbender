# Public decoding and instruction selection

This directory relates public instruction bytes and original Sail decoding to
native family, register, immediate and selector metadata. It also states
current-state fetch and selects the reference clause or explicit project profile.
Decoder-table membership is a logical connection between the public program and
witness rows, with preprocessing provenance reviewed separately.

Start with [Program](Program.lean): public bytes are read and passed to the
original Sail decoder, then projected into native family/register/immediate metadata.
The public entry record alone does not establish correct decoding.

[Columns](Columns.lean) identifies imported decoder columns.
[PooledProgram](PooledProgram.lean) combines the six admitted families and defines
logical decoder-table membership. Family projections remain in their circuit directories.
[CycleFetch](CycleFetch.lean) binds fetch to the current history state.

[Instruction](Instruction.lean) selects original clauses and the named Airbender
LW-to-x0 profile. Review that deviation separately from unchanged Sail.
[ExternalInput](ExternalInput.lean) and [PooledExternalInput](PooledExternalInput.lean)
add the pinned external-read/write-hint forms and their independent-stream connection.

Check source bytes, configuration-sensitive decoding, full metadata and selector
membership. Desired decoder answers are not independent premises. Rust preprocessing
and modeled-table provenance remain trust boundaries; these definitions do not
prove an extracted setup generator or cryptographic lookup argument.

Public initialization is in [Context](../Context/README.md); byte interpretation
and preserved history are in [Memory](../Memory/README.md).

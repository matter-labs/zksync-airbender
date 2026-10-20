# Native shift/binop tagged table

[Native](Native.lean) selects literal rows from the twelve native regions in compiled
offset order. [CSR data](NativeCsrData.lean) imports the exact compilation-test
profile: nondeterminism enabled and an empty delegation CSR list. Runtime proving/setup
CSR contents are configured separately by native code and are not bound here.

[Structural proofs](../../../../Proofs/ShiftBinop/NativeLookup.lean) retain every
stored row; [kernel tests](../../../../../Tests/ShiftArtifact.lean) check metadata,
selector preservation and actual boundary rows. Existing helper certificates
prove binary/shift results separately. Numerical instruction soundness, custom
CSR behavior and cryptographic/compiler refinement remain separate boundaries.

## Operation-specific native slot selection

[Original public decoding and native equations](../Routing.lean) now select all
four tags: SLL 47/48/49/0, SRL 47/50/51/0, SRA 47/52/50/51 and binary funct3 in
every slot. The SRA sign-fill query precedes its two logical-shift contributions.
The [complete row regressions](../../../../../Tests/ShiftRouting.lean) retain all
96 actual tagged memberships across twelve ordinary forms and x0 variants.
Exact full-word arithmetic, initialized execution and runtime CSR binding remain
separate from this table-routing connection.

## Binary query values and RV32 assembly

[The native binary result claim](../Binary.lean) now uses all four accepted byte
queries to derive exact XOR/OR/AND words and actual x0-masked writes, including
immediate forms. The [internal query equations](../../../../Proofs/ShiftBinop/BinaryQueries.lean)
retain the Mersenne31 inverse of 256; byte bounds derive both source-word bounds.
[Regressions](../../../../../Tests/ShiftBinary.lean) preserve full RV32 results
above Mersenne31 and sign-extended immediates. Native shift word assembly,
initialized execution and runtime CSR binding remain separate. Earlier sections
retain their checkpoint scope.

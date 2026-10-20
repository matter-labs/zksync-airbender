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

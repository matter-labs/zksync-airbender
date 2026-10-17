# Word-memory trace review

## Checked decoder connection

[Theorem](Decoder.lean) recovers actual public LW/SW bytes, original Sail decoding
and native metadata from the full padded logical decoder table. The
[constructor](../../../Helpers/Decoder/WordMemory.lean) keeps sign-extended
immediates, funct3=2, the native store bit, the separate x0 flag and original x0
loads. It clears only the unused rs2 on loads or rd on stores. Missing bytes,
unsupported/effectful instructions and insufficient capacity fail construction.

The separate [native registry](../../../Helpers/Context/WordMemory.lean) selects
the actual v2 artifact, all three ports, ten decoder columns and ROM tables.
Acceptance has the existing native constraint/active/state/memory meaning.
The [proof assembly](../../../../Proofs/Trace/Families/WordMemory/Decoder.lean)
rejects every minus-one padding row with the native Boolean store-mask equation.
It then derives exact zero flags, register indices, canonical PC/immediate bounds,
incoming alignment and original pure-decoder evidence. No per-row answer or table
equivalence is supplied.

[Regressions](../../../../../Tests/WordMemory.lean) construct real LW/SW bytes and
nonempty accepted native traces, including LW to x0. Negative immediates, excluded
subword/unsigned constructors, missing bytes and bad capacity are checked. A bad
zero flag passes all native constraints but full lookup membership rejects it.
This validates the separate decoder boundary; it is not an implementation defect.

## Remaining connection

This is public decoding. Public ROM words still need their actual Sail-byte
binding. Initialized word-memory read/source bounds, discarded ROM-shadow access
projection and original Sail execution/retirement remain open. The existing
arithmetic execution registry and its claims retain their scope. Physical setup
export, mixed/custom programs and cryptographic argument enforcement are separate.

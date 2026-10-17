# Findings audit

This register concerns the v2 target pinned in [provenance](artifacts/provenance.json).
V3 findings and fixes have not been established for this branch by copying their
proofs or assumptions. No v2 implementation vulnerability is established by this
backport.

## Checked scope boundaries

| Case | Evidence and disposition |
| --- | --- |
| V2 PC rollover | [Native rollover fixture](Tests/PC.lean) accepts PC 0xfffffffc to zero. The v2 proof preserves this modular behavior instead of importing the source artifact's no-overflow conclusion. This is a supported aligned path, not a reported implementation defect. |
| Local decoder/history interfaces | [Model](Airbender/Review/Circuits/AddSub/Model.lean) explicitly retains the packed decoder mask, x0 flag, preprocessing, input bounds, initial PC alignment and original Sail reads. [Selectors](Airbender/Proofs/AddSub/Selectors.lean) derives individual selector bits. Public decoding and initialized history must discharge the remaining interfaces. |
| Native clock boundary | [Clock proof](Airbender/Proofs/AddSub/Timestamp.lean) derives native advancement and port order; all per-row/prior bounds and alignment now follow from accepted logical matching and only initial clock boundaries. Typed port/state metadata is checked separately from memory-argument enforcement. |
| Stale alias reads | [Initialized-history regression](Tests/InitializedHistory.lean) shows that a second read reusing the seed timestamp passes local native row constraints but fails actual logical memory matching. This validates the separate memory boundary; it is not a v2 implementation vulnerability. The complete-history theorem derives newest preceding reads. |
| Logical initial image | [Trace memory claim](Airbender/Review/Trace/History.lean) takes explicit seed/final tokens and logical matching. [Public constructors](Airbender/Review/Helpers/Memory/PublicImage.lean) now bind seeds and initial PC to actual Sail state; subsequent operand bounds/read transport and physical boot/profile binding remain pending. No desired read/result or table-equivalence premise was introduced. |
| Decoder-owned zero flag | Native equations 24/25 use decoder variable 8 only to mask raw output into actual writes. Its Boolean/value relation comes from decoder matching, so history bounds cannot be promoted from raw-output bounds alone. Native decoder placement is checked; public table construction/membership remains pending; this is an explicit connection boundary, not an implementation defect. |
| V2 discarded writes retain decoding | Native v2 preprocessing retains the original opcode mask/operands for rd=x0, then masks the actual destination write. The prior local interface inherited an unnecessary source-style NOP restriction; it is removed. [Original Sail SUB x0,x1,x2](Tests/CircuitRows.lean) now has a checked nonzero-operand native row and public theorem application. No Rust behavior was changed. |
| Setup fidelity | [Range definitions](Airbender/Review/Helpers/Tables/Range.lean) use native Clean static tables. Their applicability to native v2 setup generation remains external. |
| Artifact fidelity | [Importer](Airbender/Import/Parse.lean) checks consumed addresses, residue bounds and unsupported features. Hashes pin the inputs; parsing/emission and native metadata interpretation are not formally proved. |

## V3 findings awaiting v2 assessment

Bigint control masks, unissued workers, worker ROM ports, decoder filler,
terminal-PC closure and contribution-mask/padding conditions must be checked
against native v2 code and artifacts before adopting a finding or a temporary
assumption. No source finding is marked resolved or accepted on v2 here.

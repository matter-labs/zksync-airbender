# Findings audit

This register concerns the v2 target pinned in [provenance](artifacts/provenance.json).
V3 findings and fixes have not been established for this branch by copying their
proofs or assumptions. No v2 implementation vulnerability is established by this
initial backport.

## Checked scope boundaries

| Case | Evidence and disposition |
| --- | --- |
| V2 PC rollover | [Native rollover fixture](Tests/PC.lean) accepts PC 0xfffffffc to zero. The v2 proof preserves this modular behavior instead of importing the source artifact's no-overflow conclusion. This is a supported aligned path, not a reported implementation defect. |
| Local decoder/history interfaces | [Model](Airbender/Review/Circuits/AddSub/Model.lean) explicitly retains the packed decoder mask, x0 flag, preprocessing, input bounds, initial PC alignment and original Sail reads. [Selectors](Airbender/Proofs/AddSub/Selectors.lean) derives individual selector bits. Public decoding and initialized history must discharge the remaining interfaces. |
| Native clock boundary | [Clock proof](Airbender/Proofs/AddSub/Timestamp.lean) derives native advancement and port order; initial/prior 19-bit bounds and alignment remain explicit until initialized history is connected. Typed port/state metadata is checked separately from memory-argument enforcement. |
| Setup fidelity | [Range definitions](Airbender/Review/Helpers/Tables/Range.lean) use native Clean static tables. Their applicability to native v2 setup generation remains external. |
| Artifact fidelity | [Importer](Airbender/Import/Parse.lean) checks consumed addresses, residue bounds and unsupported features. Hashes pin the inputs; parsing/emission and native metadata interpretation are not formally proved. |

## V3 findings awaiting v2 assessment

Bigint control masks, unissued workers, worker ROM ports, decoder filler,
terminal-PC closure and contribution-mask/padding conditions must be checked
against native v2 code and artifacts before adopting a finding or a temporary
assumption. No source finding is marked resolved or accepted on v2 here.

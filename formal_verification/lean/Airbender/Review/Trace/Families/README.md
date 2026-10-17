# Family execution review

The selected v2 arithmetic family has a short [execution theorem](AddSub/Theorems.lean)
and [original Sail step/trace aliases](AddSub/Execution.lean). The shared
[reference relation](../Execution.lean) requires actual code-byte reads, original
decoding, matching architectural PC and normal Sail preparation/execution/retirement.
Its terminal relation observes exact native PC and tracked register/RAM words.

Public inputs construct the initial image and selected setup. Native acceptance
and complete logical decoder membership derive row order, intermediate states,
operands, ranges, selectors, preprocessing and retirement. Only public RAM-cell
alignment is supplied. Calculations stay in [Proofs](../../../Proofs/Trace/Composition.lean).
Other families and physical/cryptographic argument enforcement remain pending.

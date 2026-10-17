# Shared context review

[Timestamp](Timestamps.lean) and [column](Columns.lean) definitions preserve the
source formalization's two 19-bit clock limbs, four-tick step and three ordered
port slots. Clock inputs expose initial/prior bounds and alignment; clock effects
state derived advancement and strict previous-write ordering.

[Native ADD/SUB extraction](../../../Proofs/AddSub/Timestamp.lean) connects the
v2 equations and all eight timestamp queries to the unchanged generic clock
lemmas. Initialized history still needs to supply the public clock inputs.
These local context definitions have no whole-execution dependency.

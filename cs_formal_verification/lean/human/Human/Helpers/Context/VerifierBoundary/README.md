# Public verifier boundaries

[Model.lean](Model.lean) defines public endpoint words, their native encoding and
the binding between a public statement and the row-state boundary.
[Theorems.lean](Theorems.lean) states terminal-state equality and terminal-PC bounds,
with a separate witness claim for each premise set.

State permutation and boundary binding are premises. The kernel checks their
consequences. The definitions and public binding are part of the reviewed spec.
See the [context guide](../README.md) for state and memory interfaces.

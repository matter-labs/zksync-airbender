# Padding and Fixed Trace Length

## Invariant

Padding rows must not introduce new valid computation, erase required computation, or allow state to change in ways forbidden by the intended execution semantics.

## Check

- how real rows are distinguished from padding rows
- whether the padding selector is constrained
- whether state is frozen or evolves according to a defined padding transition
- whether lookup/RAM contributions are disabled consistently
- whether final state can be moved into or out of padding
- whether padding can prematurely terminate a real operation
- whether the first padding row is constrained consistently with the last real row
- whether all remaining padding rows are constrained

## Skeptical Questions

- can the prover mark an invalid real row as padding?
- can padding suppress a required lookup or state update?
- can state be modified after the logical end of execution?
- can the trace contain holes where neither real nor padding constraints apply?

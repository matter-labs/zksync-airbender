# Public Input and Output Binding

## Invariant

Values that define the externally claimed statement must be algebraically bound to the internal execution state they are supposed to represent.

## Check

- initial state commitments
- final state commitments
- public program/image identifiers
- public outputs
- result registers
- exit status
- memory/public-data roots
- any exposed accumulator values

## Questions

- does the circuit compute the right value but fail to bind it to the public instance?
- can an internal result differ from the public result?
- are only some limbs or fields bound?
- does preprocessing introduce a public assumption that is not constrained?

If binding is performed by a global argument outside the circuit, verify the local contribution and mark the global obligation `REQUIRES_GLOBAL_AUDIT`.

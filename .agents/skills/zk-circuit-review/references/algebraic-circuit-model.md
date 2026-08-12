# Algebraic Circuit Security Model

## Relation being proved

A circuit defines an algebraic relation over a field. The prover controls private witness values and may choose any assignment accepted by every enforced relation. Witness-generation code describes one honest assignment; it does not restrict a malicious prover unless the same semantics are enforced algebraically.

The central review chain is:

```text
intended specification
  -> witness/column representation
  -> local algebraic relations and activation domains
  -> copy, lookup, permutation, zerocheck, or aggregation claims
  -> verifier/public statement
```

Audit every link relevant to the named target.

## Framework variants

### AIR-like systems

Witness values are arranged as trace columns over rows. Review per-row constraints, transition relations, first/last-row boundaries, selectors, padding, and connections to permutation or lookup arguments.

### PLONK-style systems

Review custom-gate equations, selector activation, copy/permutation constraints, lookup membership, fixed columns, and public-input wiring. An allocated value or host-language assignment is not automatically copy constrained.

### GKR and layered arithmetic circuits

Review gate semantics and wiring across layers, claimed layer outputs, fan-in/indexing, selector or multiplexing logic, degree bounds, and the connection of final outputs into Sumcheck, zerocheck, lookup, memory, or verifier claims. A correctly computed constraint value is ineffective if it is omitted from the enforced aggregate.

Some systems use row-shaped witness data at a base GKR layer. In that case apply both trace-row reasoning and layered-circuit wiring analysis.

## Integer semantics over a field

Field equations do not imply integer ranges. Bits, limbs, carries, opcodes, indices, timestamps, and enum tags require explicit constraints or sound table membership. Check recomposition and field-wrap aliases as well as individual limb ranges.

## Soundness and completeness

- Soundness fails when an invalid intended statement or transition has a satisfying algebraic assignment.
- Completeness fails when a valid intended case has no satisfying assignment or is missing from the supported relation.

Redundant constraints and inefficient encodings are not material completeness failures unless they reject an intended valid case.

## Assumed proof-system layer

A per-circuit review may assume documented proof-system primitives correctly enforce submitted claims. It must still verify the interface: declared polynomial degree, challenge timing local to the circuit, claim aggregation, public-input binding, and local contributions to external arguments.

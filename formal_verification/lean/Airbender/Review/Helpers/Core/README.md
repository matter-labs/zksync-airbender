# Core representations and references

This directory defines shared value representations and reference interfaces:
field operations, two-limb RV32 words, architectural Sail transitions and
independent stream observations. These definitions give meaning to encoded inputs
and outputs; they do not assert that an accepted circuit row implements the
reference.

## Definitions and checked representation facts

These modules define representations and reference relations rather than native
circuit soundness. The supporting [word lemmas](../../../Proofs/Arithmetic/Word.lean)
prove that RV32 conversion produces bounded limbs and round-trips to the original
bit vector, and that bounded words are determined by their numeric value.
Those facts do not make arbitrary witness limbs bounded: the consuming circuit
and history claims must establish their ranges.

Read [Field](Field.lean) and [Word](Word.lean) for the field identifier and
two-limb RV32 representation. A represented word is not automatically bounded;
check where the relevant claim proves its canonical range.

[FieldCapacity](FieldCapacity.lean) names field-size and no-wrap conditions while
preserving strict and non-strict bounds. These conditions remain generic; a
29-bit capacity requirement alone does not select BabyBear. In contrast, every
fixed coefficient in [SerializedInverse](SerializedInverse.lean) has radix times
coefficient equal to `-2013265920`. Its inverse equation forces the characteristic
to divide `2013265921`, so under primality it selects BabyBear even without a size
bound. The [checked conversions](../../../Proofs/SerializedInverse.lean) reuse
the common prime-divisor argument. Variable inverse parameters in the arithmetic
helpers remain generic. Other native fields require separately exported
coefficients and checked bindings; existing BabyBear and compatibility entrypoints
remain available.

[Sail](Sail.lean) names the architectural input/output relation and original
standard-instruction clauses. It is the reference interface, not a replacement
arithmetic semantics. [ExternalStream](ExternalStream.lean) supplies generic
stream ordering and port predicates; decoder-specific CSR forms live in
[Decoder](../Decoder/README.md).

These modules contain no accepted native trace or whole-execution contract.
Review [`properties`](../Properties.lean) independently. Pins and generation
fidelity remain recorded in the [trust document](../../../../TRUST_AND_REVIEW.md).

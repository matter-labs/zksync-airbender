# Unified reduced circuit review

This directory describes the local witness slices of the unified reduced-machine
artifact: arithmetic, control, binary/shift, memory and selected project-custom
operations or caller requests. The artifact and decoder name the native selectors and the observable
word/state effects against the relevant reference (our RV32 spec, or Clean's). Complete execution and
composition statements are kept in the unified Trace directory.

## Checked results

The [unified execution claims](../../Trace/UnifiedReduced/RVTheorems.lean) prove
the admitted standard and TRIADD/XORROT instructions retire in history-derived
order to native terminal PC/cells, with public ROM bytes and derived reads/bounds.
Those conclusions use the exact declared registry and public boot inputs.
Caller cycles and selected hash windows have separate claims; full mixed caller
retirement and control validity are not implied by local selector mappings.

[Artifact](Artifact.lean) and [Decoder](Decoder.lean) identify the unified columns, selectors and modeled setup.

The unified slices (control, jumps, binary operations, shifts, word memory,
ROM, TRIADD, XORROT) are described by the artifact, decoder and setup; the
[delegation callers](Delegation.lean) have their own module. Standard
instructions and the custom operations are both `RV.step` clauses of our spec
([RV32.lean](../../ISA/RV32.lean)).

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

[Unified shared context](../../Helpers/UnifiedReduced/README.md) binds public
initialization, current fetch and matched worker histories.
[Unified trace review](../../Trace/UnifiedReduced/README.md) owns mixed retirement,
caller cycles and selected hash windows. Those claims have different registries
and do not close full custom-CSR ABI or inactive-padding obligations.

## Field instances

The unified CPU uses a single checked instruction proof for the BabyBear and Proth120 layouts.
The host field supplies the Montgomery decoding and the byte and clock inverses. The layout
supplies the ROM boundary, lookup columns and modular constraints. Lean checks the shared
operation list against both imports. The wrap also checks two quotient limbs in its modular
path. [Field parameters](../../Helpers/Core/CircuitField.lean) · [Operation lists](../../../../proven/Proven/UnifiedReduced/Standard/Artifact.lean)

Both native execution instances reach the same RV32 terminal-state specification under their
respective ROM maps. BabyBear can dispatch workers. The wrap executes a single unified CPU
circuit. Upstream currently provides the other CPU and worker circuit artifacts in BabyBear.
[Native execution theorem](../../../../proven/Proven/UnifiedReduced/Standard/Execution.lean)

## Proth120 L1 wrap

The wrap imports its own cached unified layout over the prime field of order 7 × 2¹²⁰ + 1.
The importer decodes Montgomery coefficients at radix 2¹²⁸ and retains all 120 structured
equations. The native row theorem connects the physical gates and placements to those
equations, the 15 limb ranges, five pooled lookups, eight clock ranges and the enabled
decoder query. Its lookup premise is exact membership of the physical operands in their
public tables. [Logical artifact](Proth120Artifact.lean) · [Native row](../../Compiler/Proth120Native.lean)

The decoder uses the public program bytes. Word loads and stores use the wrap's
512 KiB ROM boundary. The four modular instructions operate on 32-bit guest words
and return the BabyBear result, including the old destination for fused multiply-add.
The two inline initialization and teardown sets each span 2²¹ rows.
[Execution](Proth120Execution.lean) · [Modular arithmetic](Proth120Modular.lean) · [Memory windows](Proth120Windows.lean)

The cached RAM outputs select the three port tuples and the PC tuple on each side
of the wrap’s single permutation. [Physical RAM wiring and encoding](../../../../proven/Proven/Compiler/Proth120Memory.lean)

The trace proof
recovers execution order and operand histories, then checks the terminal PC and tracked
cell values. CSR reads consume the independently supplied input in clock order. Padding
rows contribute identity factors. The padded theorem requires exact lookup membership
and the masked token permutation and proves one step per participating row.
[CSR rows](Proth120Input.lean) · [Native trace](../../Trace/UnifiedReduced/Proth120NativeTrace.lean) · [Padded trace](../../Trace/UnifiedReduced/Proth120Padding.lean)

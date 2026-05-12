# Picus Frontend

This crate lowers finalized Airbender circuits into Picus modules.


## What This Crate Produces

There are a few kinds of extracted programs:

- Standalone op harnesses, such as `add_op`, `xor_op`, `mul_op_signed`, `jump_op_trusted`
- Executor-family circuits, such as `add_sub_lui_auipc_mop`, `mul_div`, `shift_binop_csrrw`, `reduced_machine`
- Decoder harnesses, such as `optimized_decoder` and `unrolled_decoder`
- Delegation circuits, such as `blake2_with_extended_control_delegation` and `bigint_with_control_delegation`

The main public builders live in [`src/lib.rs`](./src/lib.rs).

## Extraction Workflow

The normal flow is:

1. Build a finalized `CircuitOutput`.
2. Convert that circuit output into a `PicusModule`.
3. Optionally partially evaluate the module under a family-specific specialization.
4. Insert the resulting module or modules into a `PicusProgram`.

The central helpers are:

- `build_picus_module_from_circuit_output(...)`
- `circuit_output_to_picus_program(...)`

`build_picus_module_from_circuit_output(...)` is the main lowering step. It reads the finalized circuit and turns:

- algebraic constraints
- booleanity constraints
- range checks
- lookups and disjunctive lookups
- optional extra explicit Picus inputs/outputs

into a single Picus module.

`circuit_output_to_picus_program(...)` is a thin wrapper that optionally specializes the module into multiple Picus modules.

## Specialization Policy

For executor-family circuits, we usually do not emit one unspecialized mega-module. Instead, we specialize on decoded family bits and emit one Picus module per interesting case.

Examples:

- `add_sub_lui_auipc_mop` emits `..._add`, `..._addi`, `..._sub`, `..._lui`, `..._auipc`, `..._addmod`, `..._submod`, `..._mulmod`
- `mul_div` emits `..._div`, `..._divu`, `..._rem`, `..._remu`, `..._mul`, `..._mulh`, `..._mulhsu`, `..._mulhu`
- `shift_binop_csrrw` emits names like `..._sll`, `..._srli`, `..._xori`, `..._csrrw`

The specialization machinery is represented by `DecoderSpecialization`.

Important rule: `cs` should not grow Picus-only builder APIs just to expose decoded bits.

Instead, this crate recovers specialization variables from the finalized circuit:

- split-bit families use `recover_split_bitmask_variables(...)`
- one-bit families use `recover_direct_mask_variable(...)`

That keeps the circuit-building API in `cs` clean.

## Current Extraction Styles

### Standalone Harnesses

Standalone harnesses build a small circuit around one operation and expose explicit Picus inputs/outputs.

Examples:

- `build_add_sub_harness(...)`
- `build_shift_harness(...)`
- `build_mul_harness(...)`
- `build_divrem_harness(...)`

These typically call `build_standalone_program(...)`.

Use this style when:

- you want one specific operation
- the boundary should be much smaller than a full executor family
- you need explicit semantic inputs/outputs rather than the default RAM-facing machine boundary

### Finalized Executor Families

Executor-family extraction usually follows this pattern:

1. Build the plain circuit output.
2. Recover the `OpcodeFamilyCircuitState` from `circuit_output.executor_machine_state`.
3. Recover the specialization variables from the finalized constraints.
4. Create a labeled `DecoderSpecialization`.
5. Call `circuit_output_to_picus_program(...)`.

Examples:

- `build_add_sub_lui_auipc_mop_picus_program()`
- `build_mul_div_picus_program()`
- `build_shift_binop_csrrw_picus_program()`
- `build_reduced_machine_picus_program()`

### Decoder Harnesses

The decoder extractors are a little different:

- `optimized_decoder` is a standalone harness with an explicit instruction input and decoded scalar outputs
- `unrolled_decoder` lowers the decoder circuit output directly and then adds extra decoder semantics

These are also used by LLZK-related flows, so the harness builders are shared carefully.

## How To Extract an Existing Circuit

The easiest path is to use the existing tests, which both validate the extraction and dump the resulting Picus programs.

Run:

```bash
cargo test -p picus_frontend
```

This writes `.picus` files into:

- [`picus_extracted_modules/`](./picus_extracted_modules)

Useful focused commands:

```bash
cargo test -p picus_frontend add_sub_lui_auipc_mop_one_hot_specialization_emits_one_module_per_bit
cargo test -p picus_frontend mul_div_specialization_emits_one_module_per_valid_pattern
cargo test -p picus_frontend shift_binop_csrrw_specialization_emits_one_module_per_valid_pattern
```

## How To Add a New Extracted Circuit

### 1. Decide the Extraction Shape

Choose one of:

- standalone harness
- finalized executor-family extraction
- decoder/delegation style extraction

If the circuit should expose machine-state boundaries and family specialization, use the finalized executor-family pattern.

If the circuit should expose a small semantic interface, use a standalone harness.

### 2. Build the Circuit Output

Add a helper in [`src/lib.rs`](./src/lib.rs) that constructs the plain circuit and returns `CircuitOutput<Mersenne31Field>`.

Examples:

- `build_add_sub_lui_auipc_mop_circuit_output()`
- `build_load_store_circuit_output()`
- `build_reduced_machine_circuit_output()`

If the circuit needs extra tables, add them before `finalize()`.

Important: do not add a new `*_with_decoded_bits` public API in `cs`.

### 3. Recover Specialization Variables If Needed

If the circuit is specialized by family mask bits:

- use `recover_split_bitmask_variables(...)` when the family parser decomposes a bitmask with `Boolean::split_into_bitmask`
- use `recover_direct_mask_variable(...)` when the family is just one boolean-backed mask

Examples:

- `add_sub_lui_auipc_mop`: split bitmask
- `jump_branch_slt`: split bitmask
- `load_store`: direct one-bit mask
- `mul_div_unsigned_only`: recover only the real split width, not padded fake bits

### 4. Define Human-Readable Specialization Labels

Prefer semantic names over raw variable assignments.

Good examples:

- `add`
- `divu`
- `srai`
- `store`

For one-hot families, use `specialization_for_flat_one_hot_named(...)`.

For custom families, build a `DecoderSpecialization` with meaningful labels.

For reduced-machine-style extractions, labels may describe a family rather than a single opcode if multiple opcodes intentionally collapse into one specialization case.

### 5. Emit the Program

Add a public builder that returns `PicusProgram`.

Typical pattern:

```rust
pub fn build_example_picus_program() -> PicusProgram {
    let (circuit_output, input, decoded_bits) = build_example_circuit_output_with_decoded_bits();
    let specialization = /* build labeled specialization */;
    circuit_output_to_picus_program(
        "example",
        &circuit_output,
        Some(&input),
        Some(&specialization),
    )
}
```

If the module does not need specialization, call `build_picus_module_from_circuit_output(...)` directly or use `circuit_output_to_picus_program(..., None)`.

### 6. Add a Smoke Test

Add a test in [`src/lib.rs`](./src/lib.rs) that:

- builds the program
- dumps it with `to_string()`
- writes it via `write_extracted_program(...)`
- checks basic invariants such as module count or expected module headers

This is the normal way extracted artifacts get regenerated.

### 7. Verify

At minimum run:

```bash
cargo check -p picus_frontend
cargo test -p picus_frontend
```

## Extra Inputs and Outputs

The default lowering is based on the finalized circuit and the machine boundary it exposes. Some circuits need additional explicit Picus-visible ports.

That is what the `extra_inputs` and `extra_outputs` parameters to `build_picus_module_from_circuit_output(...)` are for.

Typical uses:

- standalone harnesses
- decoder harnesses
- delegation circuits

If the boundary should be smaller or more semantic than the raw executor state, model those ports explicitly here rather than trying to bake them into the circuit definition.

## Naming Conventions

Specialized module names are now emitted as:

- `<base_name>_<semantic_label>`

Examples:

- `mul_div_divu`
- `shift_binop_csrrw_xori`
- `load_store_store`

If no explicit label is supplied, the partial evaluator still falls back to raw assignment-based naming. New frontend code should prefer explicit labels.

## Relationship to LLZK

This crate is not the LLZK backend, but some extraction helpers are intentionally shared with LLZK-facing flows.

Notable example:

- the optimized decoder harness is used both for Picus extraction and for LLZK witness SSA extraction

That shared logic is why some helper functions are generic over `CS` rather than directly building only a `BasicAssembly`.

## Pitfalls

- Do not add Picus-only decoded-bit APIs back into `cs`.
- Do not assume every family uses the same number of real selector bits.
- Do not forget extra tables before `finalize()`.
- Do not use unlabeled specialization names unless there is a good reason.
- Do not expose a huge machine boundary if a small semantic harness is what you actually want.

## Useful Files

- [`src/lib.rs`](./src/lib.rs): main frontend logic
- [`src/lookups.rs`](./src/lookups.rs): Picus lowering for lookup semantics
- [`picus_extracted_modules/`](./picus_extracted_modules): dumped extracted Picus programs from tests

# LOOKUP: Lookup and fixed-table interface

> Machine-facing table admission for decoder rows, fixed semantic tables, and limb
> ranges. This module stops at the local LogUp output; the proof-level reduction is not
> specified here.

`*` marks a provisional statement whose current support is implementation-only or
whose proof-level completion remains open. The corresponding gaps below state what
must be adopted or completed before promotion.

## Guarantee

Each lookup contribution is bound to a preprocessed table row. Generic lookups share
one padded setup containing the fixed semantic tables and the program-specific decoder
table. Dedicated virtual tables admit 16-bit and timestamp-limb values. The circuit
exports one rational-accumulator pair per lookup channel for proof-level completion.

This module authenticates table membership. The instruction, memory, or precompile
module that creates a query remains responsible for deriving that query from its local
state.

## Symbols

- `F = GF(p)` — base field; natural-number counts below are embedded in `F`.
- `E` — extension field in which lookup challenges and rational accumulators live.
- `n = 2^k` — trace length and setup-column length.
- `w` — generic lookup-row width, including a table ID when more than one table class
  shares the generic setup.
- `pad_w(r, id)` — `r`, followed by zero columns, followed by `id` when an ID column is
  present; the result has width `w`.
- `T_fixed` — concatenation of the initialized `TableType` rows selected by the circuit.
- `T_decoder` — program-specific decoder rows selected for the circuit family.
- `T_generic = T_fixed || T_decoder`, padded to `n` rows.
- `T_16 = [0, 1, ..., 2^16 - 1, 0, ..., 0]` — virtual 16-bit setup column of length `n`.
- `T_ts = [0, 1, ..., 2^19 - 1, 0, ..., 0]` — virtual timestamp-limb setup column of
  length `n`.
- `Q_C` — lookup contributions for channel `C`; an ordinary query has coefficient `1`,
  while the decoder query has coefficient `execute`.
- `m_C[i] : F` — multiplicity witness aligned with setup row `T_C[i]`.
- `enc_alpha(r) = sum_j alpha^j * r[j]`; single-column channels use `enc_alpha(x) = x`.

## Inputs

- **`IN-LOOKUP-001`\* — Compiled lookup instance.** `n`, the initialized fixed tables,
  the program decoder table, the declared query relations, and the three setup/output
  channel descriptions belong to one compiled circuit artifact. `|T_generic| <= n`,
  `2^19 <= n`, and the total contributing query count in each channel is less than
  `p`.

## Assumptions

- **`ASM-LOOKUP-001`\* — Query provenance.** Each contributing machine or precompile
  module constrains its query row and any activation coefficient to its local relation.
- **`ASM-LOOKUP-002`\* — Proof-level completion.** The consuming proof binds the setup,
  samples `alpha` and `beta` after the values they bind, proves the GKR reductions and
  openings, and accepts a lookup channel only when its terminal rational identity is
  zero.

## Decision tree

> Under `ASM-LOOKUP-001` and `ASM-LOOKUP-002`. Navigation view only; leaf IDs name the
> canonical statements.

- **Generic channel.**
  - **Fixed semantic-table query.** Use the selected `TableType` row under
    `REQ-LOOKUP-001`, `REQ-LOOKUP-002`, and `REQ-LOOKUP-006`.
  - **Decoder query.**
    - **`execute = 0`.** The decoder contribution has coefficient zero under
      `REQ-LOOKUP-003` and `REQ-LOOKUP-006`.
    - **`execute = 1`.** Admit the program decoder tuple under `REQ-LOOKUP-003` and
      `REQ-LOOKUP-006`.
- **16-bit range channel.** Admit the queried value under `REQ-LOOKUP-004` and
  aggregate it under `REQ-LOOKUP-006`.
- **Timestamp range channel.** Admit the queried limb under `REQ-LOOKUP-005` and
  aggregate it under `REQ-LOOKUP-006`.

## Requirements

### `REQ-LOOKUP-001`\* — Generic setup formation

The generic setup is the zero-padded concatenation

`T_generic = dump(T_fixed) || dump(T_decoder)`.

Every initialized fixed-table row is encoded as `pad_w(keys || values, table_id)`. A
decoder row is encoded as `pad_w(decoder_tuple, Decoder)`. The ID column is omitted
only when the generic setup cannot mix fixed and decoder rows.

### `REQ-LOOKUP-002`\* — Fixed semantic-table admission

A fixed-table query selecting `table_id` contributes its constrained key and value
columns, zero padding, and `table_id`. The resulting row must equal a row generated for
that `TableType` in `T_fixed`.

The generating function defines the table's implemented key/value relation. The
calling ISA or precompile module defines whether that relation is the intended one.

### `REQ-LOOKUP-003`\* — Decoder-table admission

For an executed family row, the decoder contribution is

`[pc_lo, pc_hi, rs1, rs2, rd, imm_lo, imm_hi, funct3?, family_mask?]`,

with exactly the optional columns selected by the compiled family. It must equal the
row at `pc / 4` in that family's preprocessed program table. The table contains a row
only when that PC is supported by the family. Unsupported entries are filled with
`-1`, which cannot equal a range-valid PC tuple. When `execute = 0`, this decoder query
has coefficient zero.

### `REQ-LOOKUP-004`\* — 16-bit range admission

For every declared 16-bit range query `x`:

`x in T_16`, equivalently `0 <= x < 2^16` under the canonical integer embedding in
`F`.

### `REQ-LOOKUP-005`\* — Timestamp-limb range admission

For every declared timestamp-limb range query `t`:

`t in T_ts`, equivalently `0 <= t < 2^19` under the canonical integer embedding in
`F`.

The machine-state module decides which timestamp expressions require these queries.

### `REQ-LOOKUP-006`\* — Multiplicity and local LogUp output

For each present channel `C in {generic, range16, timestamp}`, the witness contains one
multiplicity column aligned with `T_C`. Honest witness generation sets `m_C[i]` to the
number of contributing queries equal to `T_C[i]`.

For challenges `(alpha, beta)`, the compiled lookup layers construct the rational
identity

`A_C = sum_(q in Q_C) a(q) / (beta + enc_alpha(q))`
`      - sum_(i = 0)^(n - 1) m_C[i] / (beta + enc_alpha(T_C[i]))`.

They expose a numerator/denominator pair for each present channel as, respectively,
`Lookup16Bits`, `LookupTimestamps`, or `GenericLookup`. Subsequent dimension-reduction
layers preserve the sum of the represented fractions. Proof-level acceptance requires
`A_C = 0`.

## Outputs

- **`OUT-LOOKUP-001`\* — Activated-query admission.** Under `ASM-LOOKUP-002`, every query
  with a nonzero contribution coefficient equals an admitted row of its selected setup
  table. In particular, an executed decoder query belongs to `T_decoder`, a fixed
  semantic query belongs to its selected `TableType`, and range queries satisfy
  `REQ-LOOKUP-004` or `REQ-LOOKUP-005`.

## Auxiliary-argument handoff

| Channel | Setup | Witness auxiliary | Circuit output |
|---|---|---|---|
| 16-bit range | `VirtualSetupPoly::RangeCheck16Bits` | one multiplicity column | `Lookup16Bits = [num, den]` |
| timestamp limb | `VirtualSetupPoly::RangeCheckTimestamp` | one multiplicity column | `LookupTimestamps = [num, den]` |
| fixed and decoder | committed generic setup columns | one multiplicity column | `GenericLookup = [num, den]` |

These are the machine-side auxiliary inputs and outputs relevant to the W2 invocation
inventory. Their exact proof consumers belong in the proof-topology specification.

## Open boundary

- **`GAP-LOOKUP-001` — Lookup proof topology.** Identify every proof invocation that
  binds the generic and virtual setup columns, consumes the three lookup output pairs,
  performs dimension reduction, and checks the terminal zero identities, including the
  exact GKR-to-WHIR opening edges for each machine profile. Owner: proof topology.
- **`GAP-LOOKUP-002` — Lookup soundness reduction.** State the challenge order and
  domains, denominator-zero handling and PoW condition, row-compression collision
  bound, LogUp/GKR reduction theorem, and per-channel error contribution. Owner:
  soundness.
- **`GAP-LOOKUP-003` — Local lookup-contract adoption.** Review and adopt the exact
  compiled setup layout, table encodings, range-table domains, and local accumulator
  interface. They are corroborated across compiler, table, witness, and prover code,
  but no independent project reference currently designates them as intended.
  Owner: human.

## Metadata

- spec revision: TBD
- implementation: TBD
- profile: unrolled and unified-reduced machine lookup
  interface

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `IN-LOOKUP-001` | provisional | construction | — | located | `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a`; `repo:cs/src/gkr_compiler/mod.rs#GKRCircuitArtifact@dfb1b2a8a` | `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:cs/src/gkr_compiler/mod.rs#GKRCircuitArtifact` |
| `ASM-LOOKUP-001` | provisional | every query | `external:query-producing machine or precompile module` | located | `repo:cs/src/cs/circuit.rs#LookupQuery@dfb1b2a8a`; `repo:cs/src/cs/circuit_impl.rs#Circuit::enforce_lookup_tuple@dfb1b2a8a` | `symbol:cs/src/cs/circuit.rs#LookupQuery`; `symbol:cs/src/cs/circuit_impl.rs#Circuit::enforce_lookup_tuple` |
| `ASM-LOOKUP-002` | provisional | proof acceptance | `GAP-LOOKUP-001`, `GAP-LOOKUP-002`; external:proof topology and soundness | located | `repo:prover/src/gkr/prover/mod.rs#GKRProof@dfb1b2a8a`; `repo:prover/src/gkr/prover/dimension_reduction/forward.rs#evaluate_dimension_reduction_forward_with@dfb1b2a8a` | `symbol:prover/src/gkr/prover/mod.rs#GKRProof`; `symbol:prover/src/gkr/prover/dimension_reduction/forward.rs#evaluate_dimension_reduction_forward_with` |
| `REQ-LOOKUP-001` | provisional | construction | `IN-LOOKUP-001` | located | `repo:cs/src/tables/mod.rs#TableDriver::dump_tables@dfb1b2a8a`; `repo:prover/src/gkr/prover/setup.rs#GKRSetup::construct@dfb1b2a8a`; `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a` | `symbol:cs/src/tables/mod.rs#TableDriver::dump_tables`; `symbol:prover/src/gkr/prover/setup.rs#GKRSetup::construct`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask` |
| `REQ-LOOKUP-002` | provisional | fixed-table query | `ASM-LOOKUP-001`, `REQ-LOOKUP-001` | located | `repo:cs/src/tables/mod.rs#TableType::generate_table@dfb1b2a8a`; `repo:cs/src/cs/circuit_impl.rs#Circuit::enforce_lookup_tuple@dfb1b2a8a` | `symbol:cs/src/tables/mod.rs#TableType::generate_table`; `symbol:cs/src/cs/circuit_impl.rs#Circuit::enforce_lookup_tuple` |
| `REQ-LOOKUP-003` | provisional | decoder query | `ASM-LOOKUP-001`, `REQ-LOOKUP-001` | located | `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a`; `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a` | `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask` |
| `REQ-LOOKUP-004` | provisional | 16-bit range query | `ASM-LOOKUP-001`, `IN-LOOKUP-001` | located | `repo:prover/src/gkr/virtual_polys/range_check.rs#materialize_virtual_range_check_setup_poly@dfb1b2a8a`; `repo:cs/src/gkr_compiler/range_check_exprs.rs#split_range_check_exprs_from_compiler@dfb1b2a8a` | `symbol:prover/src/gkr/virtual_polys/range_check.rs#materialize_virtual_range_check_setup_poly`; `symbol:cs/src/gkr_compiler/range_check_exprs.rs#split_range_check_exprs_from_compiler` |
| `REQ-LOOKUP-005` | provisional | timestamp range query | `ASM-LOOKUP-001`, `IN-LOOKUP-001` | located | `repo:common_constants/src/timestamps.rs#TIMESTAMP_COLUMNS_NUM_BITS@dfb1b2a8a`; `repo:prover/src/gkr/virtual_polys/range_check.rs#materialize_virtual_range_check_setup_poly@dfb1b2a8a` | `symbol:common_constants/src/timestamps.rs#TIMESTAMP_COLUMNS_NUM_BITS`; `symbol:prover/src/gkr/virtual_polys/range_check.rs#materialize_virtual_range_check_setup_poly` |
| `REQ-LOOKUP-006` | provisional | present lookup channel | `IN-LOOKUP-001`, `ASM-LOOKUP-002`, `REQ-LOOKUP-001..005` | located | `repo:cs/src/gkr_compiler/lookup.rs#layout_lookup_expressions@dfb1b2a8a`; `repo:cs/src/gkr_compiler/layout.rs#GKRGraph::layout_layers@dfb1b2a8a`; `repo:prover/src/gkr/witness_gen/family_circuits/witness.rs#gkr_postprocess_multiplicities@dfb1b2a8a` | `symbol:cs/src/gkr_compiler/lookup.rs#layout_lookup_expressions`; `symbol:cs/src/gkr_compiler/layout.rs#GKRGraph::layout_layers`; `symbol:prover/src/gkr/witness_gen/family_circuits/witness.rs#gkr_postprocess_multiplicities` |
| `OUT-LOOKUP-001` | provisional | nonzero query coefficient | `ASM-LOOKUP-001`, `ASM-LOOKUP-002`, `REQ-LOOKUP-001..006` | located | `derived:REQ-LOOKUP-001..006`; `repo:prover/src/gkr/prover/debug_utils.rs#check_logup_identity@dfb1b2a8a` | `symbol:prover/src/gkr/prover/debug_utils.rs#check_logup_identity` |
| `GAP-LOOKUP-001` | open | — | affects `ASM-LOOKUP-002`, `REQ-LOOKUP-006`, `OUT-LOOKUP-001`; owner: proof topology | — | local outputs are visible in `GKRCircuitArtifact::global_output_map`, but the complete verifier invocation graph is not specified | — |
| `GAP-LOOKUP-002` | open | — | affects `ASM-LOOKUP-002`, `OUT-LOOKUP-001`; owner: soundness | — | implementation samples lookup challenges and applies PoW, but no adopted theorem/error budget is linked | — |
| `GAP-LOOKUP-003` | open | — | affects `IN-LOOKUP-001`, `ASM-LOOKUP-001`, `REQ-LOOKUP-001..006`; owner: human | — | convergent implementation evidence exists, but no independent adopted lookup-interface reference was identified | — |

# TOPO: Proof invocation topology

> Provisional W2 inventory of proof nodes and composition edges at `dfb1b2a8a`.
> Relations and soundness arguments belong to their component modules.

`*` marks an implementation-derived, provisional node or edge covered by the open
topology decisions below. It does not mean optional. A branch explicitly labeled
experimental is not yet a production claim.

## Symbols

- `P_t` — the logical program-proof bundle at recursion depth `t`.
- `C[f,k]` — chunk `k` of unrolled circuit family `f`.
- `U[k]` — chunk `k` of the unified reduced-machine circuit.
- `D[d,k]` — chunk `k` of delegation family `d`.
- `IT[k]` — unrolled initialization/teardown chunk.
- `stream_u(P)` and `stream_c(P)` — respectively the unrolled and unified
  setup-cap-prefixed nondeterminism streams built from a `ProgramProof`.

Invocation counts are execution-dependent. An indexed node denotes one proof per
present chunk; it does not assert a fixed count.

## Invocation hierarchy

> Navigation view only. Leaf IDs name the canonical topology statements.

- **Base application, unrolled machine*.** `REQ-TOPO-001`
  - `C[f,k]*`, where `f` is add/subtract, jump/branch/compare, binary/shift,
    unsigned multiply/divide, word memory, or subword memory.
  - `IT[k]*` for global initialization and teardown.
  - `D[d,k]*`, where `d` is Blake2s compression, Blake2s G-function, bigint with
    control, or Keccak-special5.
  - Each leaf is one combined `GKR + Sumcheck + WHIR/PCS` proof*. `REQ-TOPO-002`
  - `P_0` bundles the leaf proofs; the full-statement verifier consumes `P_0`
    and aggregates the per-leaf verifier outputs*. `REQ-TOPO-003`
- **Recursive continuation*.** `REQ-TOPO-004`
  - Prove `fsv_unrolled_base_layer(stream_u(P_0))` with the unrolled reduced
    machine, producing `P_1`.
  - Repeat `fsv_unrolled_recursion_layer(stream_u(P_t))` in unrolled mode while
    its estimated execution exceeds the configured switch threshold.
  - Bridge by proving that same unrolled verifier execution in unified mode,
    producing a unified `P_b`; the verified inner proof does not change.
  - Repeat `fsv_unified_recursion_layer(stream_c(P_t))` in unified mode until the
    selected terminal shape is reached.
- **Experimental L1 branch*.** `REQ-TOPO-005`
  - A delegation-free unified verifier execution is proved once over `Proth120`
    using the packed production configuration.
  - The GKR and WHIR EVM verifiers consume separate calldata views and each derive
    the same GKR-to-WHIR boundary commitment.
  - The registry records final acceptance only when both verifier bits are set for
    that commitment.

There is no separately identified aggregation-proof node at this revision. Circuit
proofs are aggregated by the full-statement verifier, and recursive compression is a
linear continuation chain rather than a proof tree.

## Requirements

### REQ-TOPO-001* — Base circuit-proof inventory

An unrolled program proof contains zero or more `C[f,k]` and `D[d,k]` proofs for
the families listed above, plus the initialization/teardown proof admitted by the
unrolled full-statement format. A unified program proof instead contains one or more
`U[k]` proofs; initialization/teardown contributions are folded into its trailing
unified chunks, while delegation proofs remain separate.

### REQ-TOPO-002* — Per-chunk proof composition

Each `C[f,k]`, `IT[k]`, `U[k]`, or `D[d,k]` invocation produces one `GKRProof`.
That object contains the layered GKR/Sumcheck messages and one `whir_proof`; WHIR is
the PCS for the committed circuit polynomials, not a sibling program-proof node.

Decoder membership and the `Generic`, `RangeCheck16`, and `TimestampRangeCheck`
lookup relations are local subrelations of the applicable compiled circuit proof.
Their claims are completed by its generated verifier. Global register, RAM, PC, and
delegation tuples contribute read-set and write-set grand products exported by the
same chunk proof. No separate decoder, lookup, range-check, or global-memory proof
object is identified at this revision.

### REQ-TOPO-003* — Full-statement composition

For each chunk proof, the full-statement verifier consumes its setup and memory
commitments and its read-set and write-set grand-product outputs. It multiplies the
products across executor, initialization/teardown, and delegation chunks, adds the
initial/final machine-state contributions, and requires the aggregate read and write
products to be equal. It also binds the program through the setup commitments and
checks the terminal program state. This verifier execution is the aggregation step
for one `P_t`.

### REQ-TOPO-004* — Recursion and continuation edges

The exact implemented proof-carrying edge is:

| Producer | Consumer | Transferred value |
|---|---|---|
| unrolled `P_0` | unrolled base-layer FSV execution | `stream_u(P_0)` as the verifier program's nondeterminism stream |
| unrolled `P_t` | unrolled recursion-layer FSV execution | `stream_u(P_t)` |
| last unrolled `P_t` | unified bridge execution of the selected unrolled FSV binary | `stream_u(P_t)` |
| unified `P_t` | unified recursion-layer FSV execution | `stream_c(P_t)` |
| each accepted layer | recursion-chain state carried by the next layer | `end_params = H(final_pc, setup_caps)` and the preceding chain preimage/hash |

The unrolled-to-unified switch threshold selects when the bridge runs; it is a
scheduling parameter, not a proof relation.

### REQ-TOPO-005* — Experimental final-verifier edge

The L1 wrapper produces one packed `Proth120` unified-circuit `GKRProof`. The EVM GKR
verifier records `(boundary_commitment, public_input, setup_commitment)` and the EVM
WHIR verifier records the independently recomputed `boundary_commitment`. The
registry state `Both` for that commitment is the identified two-transaction terminal
acceptance condition.

## Open boundary

- **GAP-TOPO-001 — Production path.** Decide which base profile, recursion path,
  Blake variant, feeder path, and L1/final-verifier branch define the production
  topology. The example pipeline and L1 driver do not make that project decision.
- **GAP-TOPO-002 — Exact invocation cardinalities.** Record, for every selected
  profile and input-size class, each circuit trace length and the formula or fixed
  value for the number of executor, initialization/teardown, delegation, recursion,
  feeder, and final-verifier invocations.
- **GAP-TOPO-003 — Invocation interfaces.** Classify every field of each invocation
  as public input `x_i`, private witness `w_i`, proved relation output, or internal
  transcript value, and map every consumed field rather than only the whole-stream
  recursion edges established above.
- **GAP-TOPO-004 — Auxiliary edge expansion.** Map each decoder/lookup/range-check
  claim and each GKR-to-WHIR opening claim to its exact committed polynomial,
  generated-verifier input, and completion predicate. This is missing topology and
  relation detail, not a claim that separate proofs exist.
- **GAP-TOPO-005 — Terminal artifact.** Establish the concrete feeder-to-L1 input
  edge, deployed contract identities, calldata derivation, and external acceptance
  consumer for the intended terminal artifact.

## Metadata

- spec revision: TBD
- implementation: TBD
- profile: `unrolled IM base -> unrolled reduced continuation -> unified reduced continuation; experimental Proth120 L1 branch`
- configured security level: `Sec100`; exact per-trace WHIR schedules remain under
  `GAP-TOPO-002`
- W2 coverage: [official `REQ-W2-003..004,007`](../ETHPROOFS-W2.md#deliverable-requirements)

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `REQ-TOPO-001` | provisional | each program execution | — | located | `repo:program_prover/src/unrolled.rs#prove_unrolled_execution_with_replayer@dfb1b2a8a`; `repo:program_prover/src/unified.rs#prove_unified_execution_with_replayer@dfb1b2a8a` | `symbol:program_prover/src/unrolled.rs#prove_unrolled_execution_with_replayer`; `symbol:program_prover/src/unified.rs#prove_unified_execution_with_replayer` |
| `REQ-TOPO-002` | provisional | each present circuit chunk | `REQ-TOPO-001` | located | `repo:prover/src/gkr/prover/mod.rs#GKRProof@dfb1b2a8a`; `repo:verifier_evm/ARCHITECTURE.md#Individual Proofs@dfb1b2a8a` | `symbol:prover/src/gkr/prover/mod.rs#GKRProof`; `symbol:prover/src/gkr/prover/mod.rs#prove_configured_with_gkr_with_backends`; `symbol:prover/src/gkr/prover_config/example_configs.rs#config_for_security_level_under_pessimistic_conjecture` |
| `REQ-TOPO-003` | provisional | full-statement verification | `REQ-TOPO-001..002` | located | `repo:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits@dfb1b2a8a`; `repo:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit@dfb1b2a8a` | `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `REQ-TOPO-004` | provisional | recursive proving | `REQ-TOPO-003` | located | `repo:circuit_defs/prover_examples/src/recursion.rs#test_recursive_proving_pipeline_zksync_os@dfb1b2a8a`; `repo:full_statement_verifier/src/host_utils/mod.rs#build_unrolled_stream@dfb1b2a8a` | `symbol:circuit_defs/prover_examples/src/recursion.rs#test_recursive_proving_pipeline_zksync_os`; `symbol:full_statement_verifier/src/host_utils/mod.rs#build_unrolled_stream`; `symbol:full_statement_verifier/src/host_utils/mod.rs#build_unified_stream`; `symbol:full_statement_verifier/src/host_utils/mod.rs#unified_switch_cycles` |
| `REQ-TOPO-005` | provisional | experimental L1 branch | `REQ-TOPO-002, REQ-TOPO-004` | located | `repo:circuit_defs/prover_examples/src/l1.rs#prove_l1_wrap_in_recompute_mode@dfb1b2a8a`; `repo:verifier_evm/src/templates/GkrWhirRegistry.sol#GkrWhirRegistry@dfb1b2a8a` | `symbol:circuit_defs/prover_examples/src/l1.rs#prove_l1_wrap_in_recompute_mode`; `symbol:prover/src/tests/gkr/large_field.rs#evm_production_packed_prover_config`; `symbol:verifier_evm/src/templates/GkrWhirRegistry.sol#GkrWhirRegistry` |
| `GAP-TOPO-001` | open | — | affects `REQ-TOPO-001, REQ-TOPO-004..005`; owner: human | — | multiple selectable implementation paths at `dfb1b2a8a` | — |
| `GAP-TOPO-002` | open | — | affects `REQ-TOPO-001, REQ-TOPO-004..005`; owner: specification | — | execution-dependent vectors in `ProgramProof`; profile/config inventory incomplete | — |
| `GAP-TOPO-003` | open | — | affects `REQ-TOPO-001..005`; owner: specification | — | `ProgramProof` serialization exists, but W2 `x_i/w_i/output_i` classification is absent | — |
| `GAP-TOPO-004` | open | — | affects `REQ-TOPO-002..003`; owner: specification | — | compiled-circuit and generated-verifier crosswalk not yet recorded | — |
| `GAP-TOPO-005` | open | — | affects `REQ-TOPO-005`; owner: human and specification | — | L1 driver and contract templates do not establish the intended deployed terminal consumer | — |

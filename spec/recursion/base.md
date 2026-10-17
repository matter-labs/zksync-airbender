# BASE: Base-proof acceptance

> Specifies acceptance of the unrolled full-unsigned base proof and its program
> binding. Recursive continuation and terminal external verification belong to
> `TOPO`.

`*` after an ID marks a provisional relation whose exact base-acceptance policy is
currently implementation-derived or affected by an unresolved boundary below.

## Guarantee

An accepted base artifact proves one execution under the unrolled full-unsigned
machine profile, closes the combined machine-state, memory, and delegation products,
and returns eight program-output words plus a chain value bound to the supplied
program's exit point and setup commitments.

## Symbols and inputs

- `B_bytes`, `T_bytes` — supplied program-image and text-section bytes.
- `B`, `T` — their padded `u32` word representations used to construct proving
  setups.
- `exit(B) : u32` — byte address of the last instruction in the unique
  `EXIT_SEQUENCE` occurrence in `B`.
- `Caps(B,T)` — setup caps recomputed for `(B,T)` under the unrolled full-unsigned
  base profile, ordered by circuit-family identifier.
- `Caps_claim` — setup-cap prefix consumed by the unrolled full-statement verifier.
- `H` — the configured Blake2s transcript hash to eight `u32` words.
- `PCBlock(pc) = pc || 0^15` — one 16-word block; final timestamp words are zero in
  this block.
- `EP(pc,Caps) = H(PCBlock(pc) || flatten(Caps))` — program end parameters.
- `Chain0(ep) = H(0^8 || ep)` — base recursion-chain value.
- `Reg_f[r] : u32` and `rts_f[r]` — final value and last-access timestamp for
  register `r in [0,32)`.
- `pc_f : u32`, `ts_f` — final program counter and machine timestamp.
- `GP_R`, `GP_W` — aggregate read-set and write-set products after all proof and
  boundary contributions.
- `A` — the submitted base `ProofArtifact` and its contained `ProgramProof`.
- `Y : [0,16) -> u32` — the accepted full-statement-verifier output.

- **IN-BASE-001* — Supplied program.** Setup construction succeeds for `(B,T)`, and
  `B` contains exactly one contiguous `EXIT_SEQUENCE`.
- **IN-BASE-002* — Base artifact.** `A` contains the setup caps, circuit and
  delegation proofs, initialization/teardown proof, final machine-state values,
  transcript challenges, proof-of-work value, chain metadata, and target metadata
  consumed by base verification.

## Assumptions

- **ASM-BASE-001* — Machine relations.** Accepted executor and
  initialization/teardown proof outputs expose the machine state and local global-
  argument contributions specified by `external:MACH`, `external:REG`,
  `external:MEM`, and `external:CONT`.
- **ASM-BASE-002* — Global-argument soundness.** Equality of the aggregated read and
  write products establishes the register, PC, RAM/ROM, and delegation consistency
  claimed by their external modules. Its error bound belongs to `external:SOUND`.
- **ASM-BASE-003* — Proof invocation soundness.** Every invoked circuit verifier
  enforces the relation represented by its output, under the invocation inventory and
  edges in `REQ-TOPO-001..003`.
- **ASM-BASE-004* — Cryptographic binding.** Transcript challenges, setup
  commitments, `H`, and the artifact's program hashes have the binding properties
  assigned by `external:TRANS` and `external:SOUND`.

## Acceptance tree

> Interpret the tree under `ASM-BASE-001..004`. It is a navigation view; the leaf
> IDs name the canonical checks below.

- **`A.target != Base`, or the claimed chain has other than one layer.** Violates
  `REQ-BASE-001`.
- **Base target with one claimed layer.**
  - **Artifact schema, security profile, or supplied-program hashes disagree.**
    Violates `REQ-BASE-001`.
  - **A proof invocation, transcript challenge, or setup-cap check fails.** Violates
    `REQ-BASE-002` or `REQ-BASE-003`.
  - **The global products or terminal-register conditions fail.** Violates
    `REQ-BASE-004` or `REQ-BASE-005`.
  - **The claimed chain metadata or verifier output differs from the trusted
    program chain.** Violates `REQ-BASE-006` or `REQ-BASE-007`.
  - **All checks hold.** `OUT-BASE-001`.

## Requirements

### REQ-BASE-001* — Base target and supplied-program association

Acceptance requires:

- `A.target = Base` and `length(A.chain_end_params) = 1`;
- `A.schema_version` and `A.security_level` equal the verifier's compiled values;
- `A.program_bin_keccak = Keccak256(B_bytes)`; and
- `A.program_text_keccak = Keccak256(T_bytes)`.

### REQ-BASE-002* — Proof and challenge acceptance

Every executor, initialization/teardown, and delegation proof selected by the base
topology verifies. All present chunk proofs use one claimed set of external challenges,
and those challenges equal the challenges redrawn from the transcript seed and
proof-of-work value.

### REQ-BASE-003* — Setup authentication

For each accepted unrolled executor proof, its verifier-reported setup cap equals the
matching cap in `Caps_claim`. Each accepted delegation proof uses the configured cap
for its delegation type. Exactly one initialization/teardown proof is accepted; no
program-specific setup-cap comparison is applied to that invocation.

### REQ-BASE-004* — Boundary state and global closure

The global write product includes the initial boundary

- `Reg[r] <- 0` at timestamp `0`, for every `r in [0,32)`; and
- `pc <- 0` at timestamp `4`.

The global read product includes `(Reg_f[r], rts_f[r])` for every register and
`(pc_f, ts_f)`. Multiplying these boundary terms with every accepted executor,
initialization/teardown, and delegation contribution yields

`GP_R = GP_W`.

### REQ-BASE-005* — Terminal registers and program output

`Reg_f[0] = 0`, `Reg_f[r] = 0` for every `r in [18,26)`, and

`Y[0..8] = Reg_f[10..18]`.

No other final register value is exported by this base relation.

### REQ-BASE-006* — Proved base chain

The unrolled full-statement verifier computes

`ep_claim = EP(pc_f, Caps_claim)`

and returns

`Y[8..16] = Chain0(ep_claim)`.

`ts_f` participates in `REQ-BASE-004` and in the transcript, but not in `ep_claim`.

### REQ-BASE-007* — Trusted exit and program binding

The artifact verifier independently computes

`ep_trusted = EP(exit(B), Caps(B,T))`

and requires

- `A.chain_end_params = [ep_trusted]`;
- `A.chain_preimage = 0^8 || ep_trusted`;
- `A.chain_hash = Chain0(ep_trusted)`; and
- `Y[8..16] = A.chain_hash`.

This is the implemented acceptance check that binds the proved `pc_f` and
`Caps_claim` to the supplied program's unique exit point and recomputed setups under
`ASM-BASE-004`.

## Derived facts

- **Initial boundary**
  `Reg[r] <- 0` at timestamp `0` for every `r in [0, 32)`
  `pc <- 0` at timestamp `4`
- **Global closure**
  `GP_R = GP_W`
- **Program-chain binding**
  `Y[8..16] = Chain0(EP(pc_f, Caps_claim))`
  `Y[8..16] = Chain0(EP(exit(B), Caps(B,T)))`
- **Output domain**
  `Y in u32^16`
  `Y[0..8] = Reg_f[10..18]`
- **End-parameter inputs**
  `ep_claim = EP(pc_f, Caps_claim)`
  `ts_f` is excluded from `ep_claim`

## Outputs

- **OUT-BASE-001* — Base verifier output.** On acceptance,
  `Y = Reg_f[10..18] || Chain0(EP(exit(B), Caps(B,T)))`. This is the value handed to
  the continuation edge specified by `REQ-TOPO-004`, or returned for the base proof
  target.

## Open boundary

- **GAP-BASE-001 — Invocation interfaces.** Classify every consumed proof/artifact
  field as public input, private witness, proved output, or internal transcript value,
  and name every exact producer/consumer edge. This is the base-specific instance of
  `GAP-TOPO-003..004`.
- **GAP-BASE-002 — End-parameter timestamp policy.** Decide whether omitting `ts_f`
  from `EP` is intended normative behavior. The implementation authenticates it in
  the transcript and global argument but zeros its two words before hashing `EP`.
- **GAP-BASE-003 — External base-result boundary.** Specify which consumer, if any,
  treats `Y[0..8]` as a public application output when the selected terminal target is
  `Base`; current code returns the words, while the terminal artifact policy remains
  open in `TOPO`.
- **GAP-BASE-004 — Base-acceptance policy adoption.** Review and adopt the exact
  supplied-program domain, artifact schema, proof inventory, setup authentication,
  global closure, terminal-register policy, and exported base value. These relations
  currently describe the verifier implementation but are not yet backed by an
  independent project acceptance-policy reference.

## Metadata

- spec revision: TBD
- implementation: TBD
- profile: `unrolled full-unsigned base; Sec100 full-statement verifier`
- W2 coverage: [official `REQ-W2-001,003..004,007`](../ETHPROOFS-W2.md#deliverable-requirements)

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `IN-BASE-001` | provisional | supplied base program | — | located | `repo:circuit_defs/setups/src/program_setups.rs#find_binary_exit_point@dfb1b2a8a`; `repo:circuit_defs/setups/src/program_setups.rs#compute_unrolled_program_setups@dfb1b2a8a` | `symbol:circuit_defs/setups/src/program_setups.rs#find_binary_exit_point`; `symbol:circuit_defs/setups/src/program_setups.rs#compute_unrolled_program_setups` |
| `IN-BASE-002` | provisional | submitted artifact | — | located | `repo:prover_pipeline/src/lib.rs#ProofArtifact@dfb1b2a8a`; `repo:full_statement_verifier/src/program_proof.rs#ProgramProof@dfb1b2a8a` | `symbol:prover_pipeline/src/lib.rs#ProofArtifact`; `symbol:full_statement_verifier/src/program_proof.rs#ProgramProof` |
| `ASM-BASE-001` | provisional | each accepted chunk | `external:MACH`; `external:REG`; `external:MEM`; `external:CONT` | prose | direct machine-module interfaces | — |
| `ASM-BASE-002` | provisional | global-product equality | `external:LOOKUP`; `external:MEM`; `external:SOUND` | located | `repo:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions@dfb1b2a8a` | `symbol:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions` |
| `ASM-BASE-003` | provisional | every invoked proof | `REQ-TOPO-001..003`; `external:GKR`; `external:WHIR` | prose | [proof topology](topology.md) | — |
| `ASM-BASE-004` | provisional | transcript and program binding | `external:TRANS`; `external:SOUND` | prose | [soundness accounting](../soundness/accounting.md) | — |
| `REQ-BASE-001` | provisional | artifact verification | `IN-BASE-001..002` | located | `repo:prover_pipeline/src/lib.rs#verify_artifact@dfb1b2a8a`; `repo:prover_pipeline/src/lib.rs#load_and_validate_program@dfb1b2a8a` | `symbol:prover_pipeline/src/lib.rs#verify_artifact`; `symbol:prover_pipeline/src/lib.rs#load_and_validate_program` |
| `REQ-BASE-002` | provisional | base full-statement verification | `ASM-BASE-003..004`; `REQ-TOPO-001..003` | located | `repo:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits@dfb1b2a8a` | `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits` |
| `REQ-BASE-003` | provisional | each accepted proof invocation | `ASM-BASE-003`; `REQ-BASE-002` | located | `repo:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits@dfb1b2a8a` | `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_unrolled_base_layer_sec_100` |
| `REQ-BASE-004` | provisional | base full-statement verification | `ASM-BASE-001..003`; `REQ-BASE-002` | located | `repo:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits@dfb1b2a8a`; `repo:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions@dfb1b2a8a` | `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions` |
| `REQ-BASE-005` | provisional | `BASE_LAYER = true` | `REQ-BASE-002`, `REQ-BASE-004` | located | `repo:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits@dfb1b2a8a` | `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits` |
| `REQ-BASE-006` | provisional | `BASE_LAYER = true` | `REQ-BASE-003..005`; `ASM-BASE-004` | located | `repo:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits@dfb1b2a8a`; `repo:full_statement_verifier/src/recursion_chain.rs#compute_end_params@dfb1b2a8a` | `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/recursion_chain.rs#compute_end_params`; `symbol:full_statement_verifier/src/recursion_chain.rs#RecursionChain::begin` |
| `REQ-BASE-007` | provisional | artifact verification for `Base` | `IN-BASE-001`; `REQ-BASE-001`, `REQ-BASE-006`; `ASM-BASE-004` | located | `repo:prover_pipeline/src/lib.rs#trusted_end_params@dfb1b2a8a`; `repo:prover_pipeline/src/lib.rs#expected_chain_end_params@dfb1b2a8a`; `repo:prover_pipeline/src/lib.rs#ensure_recursion_chain_binds_program@dfb1b2a8a` | `symbol:prover_pipeline/src/lib.rs#trusted_end_params`; `symbol:prover_pipeline/src/lib.rs#expected_chain_end_params`; `symbol:prover_pipeline/src/lib.rs#ensure_recursion_chain_binds_program` |
| `OUT-BASE-001` | provisional | accepted base artifact | `REQ-BASE-005..007` | located | `repo:prover_pipeline/src/lib.rs#verify_artifact@dfb1b2a8a` | `symbol:prover_pipeline/src/lib.rs#verify_artifact`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_unrolled_base_layer_sec_100` |
| `GAP-BASE-001` | open | — | affects `IN-BASE-002`, `REQ-BASE-002..003`, `OUT-BASE-001`; owner: specification | — | `GAP-TOPO-003..004` | — |
| `GAP-BASE-002` | open | — | affects `REQ-BASE-006..007`; owner: human | — | final timestamp words are zeroed before `end_params` hashing at `dfb1b2a8a` | — |
| `GAP-BASE-003` | open | — | affects `OUT-BASE-001`; owner: human | — | base verifier output is returned by `verify_artifact`; terminal consumer remains profile-dependent | — |
| `GAP-BASE-004` | open | — | affects `IN-BASE-001..002`, `ASM-BASE-001..004`, `REQ-BASE-001..007`, `OUT-BASE-001`; owner: human | — | current acceptance policy is recovered from verifier and pipeline code without an independent adopted project reference | — |

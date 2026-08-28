# BASE: Base-Proof Statement

> Draft extraction. Reconcile against the current implementation and move inline
> provenance into a metadata appendix before treating this module as current.

- spec-revision: `2026-08-28.5`
- implementation: `matter-labs/zksync-airbender@0aa0d393bc98fa46a2b0365d2636a98a0409b606+dirty`
- profile: `airbender-v3-gkr-2026-08-11; base=P_base`
- scope: `base proof acceptance, program binding, termination, and output`

## Symbols

- `B : [0,n) -> u32` — padded binary image
- `T : [0,m) -> u32` — padded text section
- `P_base` — full-unsigned base-program profile
- `EXIT_SEQUENCE = [0x000d2503, 0x004d2583, 0x008d2603, 0x00cd2683, 0x010d2703, 0x014d2783, 0x018d2803, 0x01cd2883, 0x020d2903, 0x024d2983, 0x028d2a03, 0x02cd2a83, 0x030d2b03, 0x034d2b83, 0x038d2c03, 0x03cd2c83, 0x0000006f]`
- `count_contiguous(B,X)` — number of contiguous occurrences of word sequence `X` in `B`
- `Caps(B,T)` — ordered committed setup caps recomputed for `(B,T,P_base)`
- `Caps_claim` — setup caps consumed by the base verifier
- `H` — configured Blake2s transcript hash to eight `u32` words
- `exit(B)` — byte address of the final word of the unique `EXIT_SEQUENCE` in `B`
- `EP(B,T) = H(exit(B) || 0^15 || Caps(B,T))` — program end parameters
- `Reg_f : [0,32) -> u32` — final register values
- `rts_f : [0,32) -> [0,2^38)` — final register-access timestamps
- `pc_f : u32` — final program counter
- `ts_f : [0,2^38)` — final machine timestamp
- `GP_R`, `GP_W` — aggregated global read/write products after boundary contributions
- `Chain_0(B,T) = H(0^8 || EP(B,T))`
- `Out : [0,16) -> u32` — base verifier output
- `Accept_base(B,T,claim) : {0,1}` — end-to-end base-claim acceptance
- `0^k` — sequence of `k` zero `u32` words
- `X || Y` — sequence concatenation

## Inputs

### IN-BASE-001
- status: `provisional`
- statement: `(B,T) satisfies IN-MACH-002 under P_base`
- source: `../machine/execution.md#IN-MACH-002`

### IN-BASE-002
- status: `provisional`
- statement: `claim = (Reg_f, rts_f, pc_f, ts_f, circuit_proofs, external_challenges, pow_challenge)`
- source: `repo:full_statement_verifier/src/program_proof.rs#ProgramProof@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### IN-BASE-003
- status: `provisional`
- statement: `B contains exactly one contiguous EXIT_SEQUENCE`
- source: `repo:circuit_defs/setups/src/program_setups.rs#find_binary_exit_point@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

## Assumptions

### ASM-BASE-001
- status: `provisional`
- statement: `OUT-MACH-001 holds for (B,T,P_base,Reg_f,pc_f,ts_f)`
- discharged-by: `../machine/execution.md#OUT-MACH-001`

### ASM-BASE-002
- status: `provisional`
- statement: `each accepted GKR proof enforces its declared circuit output relation`
- discharged-by: `external:GKR`

### ASM-BASE-003
- status: `provisional`
- statement: `H is collision-resistant for all transcript domains used below`
- discharged-by: `external:TRANS`

## Decision tree

> Under `ASM-BASE-001..003`. Experimental navigation view; leaf IDs name canonical
> statements.

- **`count_contiguous(B, EXIT_SEQUENCE) != 1`.** Reject the input. `REJ-BASE-001`.
- **`count_contiguous(B, EXIT_SEQUENCE) = 1`.**
  - **`Caps_claim != Caps(B,T)`.** No accepting proof. `REJ-BASE-002`.
  - **`Caps_claim = Caps(B,T)`.**
    - **`pc_f != exit(B)`.** Reject the end-to-end claim. `REJ-BASE-003`.
    - **`pc_f = exit(B)`.**
      - **Any remaining terminal relation fails.** No accepting proof.
        `REQ-BASE-003..010`.
      - **All terminal relations hold.** Export `OUT-BASE-001` and `OUT-BASE-002`.

Within the assumed domain, the successful leaf includes the machine, global-product,
terminal-register, end-parameter, chain, and output relations in `REQ-BASE-003..010`.

## Requirements

### REQ-BASE-001
- status: `provisional`
- statement: `pc_f = exit(B)`
- depends: `IN-BASE-003`, `ASM-BASE-001`
- source: `profile:airbender-v3-gkr-2026-08-11#Initialization, output, and termination; repo:tools/cli/src/prover_utils.rs#trusted_end_params@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-BASE-002
- status: `provisional`
- statement: `every circuit proof uses the corresponding cap in Caps(B,T)`
- depends: `IN-BASE-001`, `ASM-BASE-002`
- source: `repo:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits@0aa0d393bc98fa46a2b0365d2636a98a0409b606; repo:circuit_defs/setups/src/program_setups.rs#compute_unrolled_program_setups@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-BASE-003
- status: `provisional`
- statement: `GP_R = GP_W after adding initial writes (forall r: register[r]=0 at timestamp 0; pc=0 at timestamp 4) and final reads (Reg_f,rts_f,pc_f,ts_f)`
- depends: `ASM-BASE-001`, `ASM-BASE-002`
- source: `repo:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-BASE-004
- status: `normative`
- statement: `Reg_f[0] = 0`
- depends: `ASM-BASE-001`
- source: `../machine/execution.md#INV-MACH-001`

### REQ-BASE-005
- status: `provisional`
- statement: `forall j in [18,26): Reg_f[j] = 0`
- depends: `ASM-BASE-001`
- source: `profile:airbender-v3-gkr-2026-08-11#Initialization, output, and termination; repo:full_statement_verifier/src/unrolled_proof_statement.rs#BASE_LAYER@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-BASE-006
- status: `provisional`
- statement: `EP(B,T) = H(exit(B) || 0^15 || Caps(B,T))`
- depends: `REQ-BASE-001`, `REQ-BASE-002`, `ASM-BASE-003`
- source: `repo:full_statement_verifier/src/recursion_chain.rs#compute_end_params@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-BASE-007
- status: `provisional`
- statement: `Chain_0(B,T) = H(0^8 || EP(B,T))`
- depends: `REQ-BASE-006`, `ASM-BASE-003`
- source: `repo:full_statement_verifier/src/recursion_chain.rs#RecursionChain::begin@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-BASE-008
- status: `provisional`
- statement: `forall j in [0,8): Out[j] = Reg_f[10+j]`
- depends: `ASM-BASE-001`
- source: `profile:airbender-v3-gkr-2026-08-11#Initialization, output, and termination; repo:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-BASE-009
- status: `provisional`
- statement: `forall j in [0,8): Out[8+j] = Chain_0(B,T)[j]`
- depends: `REQ-BASE-005`, `REQ-BASE-007`
- source: `repo:full_statement_verifier/src/unrolled_proof_statement.rs#BASE_LAYER@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-BASE-010
- status: `provisional`
- statement: `ts_f is included in REQ-BASE-003 and excluded from EP(B,T)`
- depends: `REQ-BASE-003`, `REQ-BASE-006`
- source: `repo:full_statement_verifier/src/unrolled_proof_statement.rs#final_pc_buffer@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

## Preserved invariants

### INV-BASE-001
- status: `provisional`
- statement: `Accept_base(B,T,claim) => Caps_claim = Caps(B,T)`
- depends: `REQ-BASE-002`
- source: `derived:REQ-BASE-002`

### INV-BASE-002
- status: `provisional`
- statement: `Accept_base(B,T,claim) => GP_R = GP_W`
- depends: `REQ-BASE-003`
- source: `derived:REQ-BASE-003`

## Rejections

### REJ-BASE-001
- status: `provisional`
- statement: `count_contiguous(B, EXIT_SEQUENCE) != 1 => input rejected`
- depends: `IN-BASE-003`
- source: `repo:circuit_defs/setups/src/program_setups.rs#find_binary_exit_point@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REJ-BASE-002
- status: `provisional`
- statement: `Caps_claim != Caps(B,T) => no accepting proof`
- depends: `REQ-BASE-002`
- source: `repo:full_statement_verifier/src/unrolled_proof_statement.rs#setup_caps@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REJ-BASE-003
- status: `provisional`
- statement: `pc_f != exit(B) => end-to-end base claim rejected`
- depends: `REQ-BASE-001`, `REQ-BASE-006`
- source: `repo:tools/cli/src/prover_utils.rs#expected_chain_end_params@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

## Outputs

### OUT-BASE-001
- status: `provisional`
- statement: `Out = Reg_f[10..18] || Chain_0(B,T)`
- depends: `REQ-BASE-008`, `REQ-BASE-009`
- source: `derived:REQ-BASE-008+REQ-BASE-009`

### OUT-BASE-002
- status: `provisional`
- statement: `EP(B,T) binds exit(B) and Caps(B,T), but not ts_f`
- depends: `REQ-BASE-006`, `REQ-BASE-010`
- source: `derived:REQ-BASE-006+REQ-BASE-010`

## Gaps

### GAP-BASE-001
- status: `open`
- question: `Which initial register values and timestamps are normative inputs to the base statement?`
- affects: `REQ-BASE-003`, `ASM-BASE-001`
- evidence: `profile delegates register initialization to global state; no normative initial-register document identified`
- owner: `human`

### GAP-BASE-002
- status: `open`
- question: `Which prover input words are public statement inputs, committed private inputs, or unconstrained nondeterminism?`
- affects: `IN-BASE-002`, `OUT-BASE-001`
- evidence: `tools/cli/src/prover_utils.rs#Prover::prove_words@0aa0d393bc98fa46a2b0365d2636a98a0409b606; no normative visibility contract identified`
- owner: `human`

### GAP-BASE-003
- status: `open`
- question: `Are final register-access timestamps statement data or verifier-internal witnesses only?`
- affects: `IN-BASE-002`, `REQ-BASE-003`
- evidence: `repo:full_statement_verifier/src/program_proof.rs#register_final_values@0aa0d393bc98fa46a2b0365d2636a98a0409b606; absorbed by transcript but omitted from Out`
- owner: `human`

### GAP-BASE-004
- status: `open`
- question: `Is exclusion of ts_f from EP(B,T) a normative requirement?`
- affects: `REQ-BASE-010`, `OUT-BASE-002`
- evidence: `implementation explicitly zeros timestamp words before hashing end_params; profile documents final-PC/setup binding only`
- owner: `human`

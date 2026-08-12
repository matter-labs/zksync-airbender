# GKR EVM verifier — STEP 1 reference: transcript init (MergedAndPackedMemoryAndWitness)

Validated in pure Rust against `prover/unified_circuit_proof_proth120.json` by the test
`prover/src/tests/gkr/large_field.rs::validate_packed_transcript_recipe` (fast; no proving).
The derived nonce and `GKRExternalChallenges` match the proof exactly.

## Field
Proth120: `P = 7*2^120 + 1 = 0x7000000000000000000000000000001` (same as whir.sol). One
`uint128` per element. Transcript hash = keccak256.

## Recipe the Solidity `transcript_init` must implement

1. Build a u32 stream `transcript_input` (in order):
   - `inits_and_teardowns_top_bits`  — `proof.inits_and_teardowns_top_bits: Vec<u32>`
   - setup cap digests               — `proof.whir_proof.setup_commitment.commitment.cap.cap`
     (each digest is `[u32; 8]`, flattened word-by-word; included because the setup has columns)
   - merged (mem+wit) cap digests    — `proof.whir_proof.memory_commitment.commitment.cap.cap`
     (each digest `[u32; 8]`; this is the packed base commitment cap)
2. `seed = keccak256( each u32 as 4 LITTLE-endian bytes, concatenated )`
3. PoW-gated draw of `TOTAL_CHALLENGES + 2 = 9` field elements:
   - `pow_bits = max(lookup_challenges_pow_bits(80, lookup_identity_degree(circuit)), external_pow_bits)`
     → for this circuit = **0**.
   - fold nonce in unconditionally: `seed = keccak256(seed || nonce_be8)` (nonce=0 here → 8 zero bytes).
   - then draw 9 elements; each draw: `seed = keccak256(seed)`, take `bytes[0..16]` as **big-endian**
     u128, reduce mod P.
   - `challenges[0..7]` → `GKRExternalChallenges` (6 linearization + 1 additive),
     `challenges[7..9]` → `[lookup_alpha, lookup_additive_part]`.

Field element ABSORB (elsewhere in the transcript): `seed = keccak256(seed || BE16(el)...)`.
PoW verify: `digest = keccak256(seed || nonce_be8)`; assert top `pow_bits` bits zero; `seed = digest`.

## Reference values for THIS proof (basic_fibonacci, 2^22, pack_log2=4)
- seed after commit_initial_u32 = `0x26509dbe5c7a38348f24997eca31f7c9fbec8d61f4d8a0038292836975f1d62a`
- lookup pow_bits = 0 ; pow nonce = 0
- challenges (as `0x{:032x}` u128, index → meaning):
  - [0] `0x069daed5dbcc43f1a7b83e738e6000a0`  perm addr_low
  - [1] `0x032dad98f0c5fae7307259608a67ac6e`  perm addr_high
  - [2] `0x053efcfc827ed9003e569e68329cb736`  perm ts_low
  - [3] `0x06dadad22ecbaed9e13f9141f6a7b981`  perm ts_high
  - [4] `0x0110efef202b58876924c46309615d05`  perm value_low
  - [5] `0x05cf1667ee0389f548469e0ccb27f685`  perm value_high
  - [6] `0x06a76fd69d68798f727ab895b707ac52`  perm additive_part
  - [7] `0x02a48105e1ef1781ab2fc61d5e007ebf`  lookup_alpha
  - [8] `0x02d32afd101f3211f4f2f705bf194b54`  lookup_additive_part

(Regenerate/verify anytime: `cd prover && RUSTFLAGS="-C debuginfo=0" cargo test -p prover --lib validate_packed_transcript_recipe -- --nocapture`)

---

## STEP 2a — GKR dimension-reducing ENTRY (validated on-chain: `GkrStep1.gkrEntry`)

After the 9 STEP-1 challenges, the verifier COMBINES the circuit outputs to seed the
dimension-reducing sumcheck:
1. absorb every output evaluation: `seed = keccak256(seed || outputEvals)`, where
   `outputEvals` = each field element as 16-byte BE, iterating `final_explicit_evaluations`
   in `OutputType` order (PermutationProduct, Lookup16Bits, LookupTimestamps, GenericLookup,
   InitsAndTeardownsProduct), `[0]` (read/num) then `[1]` (write/den). Here 5 outputs × 2 ×
   2^4 = 160 elems = 2560 bytes.
2. draw `final_trace_size_log_2 + 1` field elements (= 5 here): first 4 = `eval_point`,
   last = `batching`.
3. initial 10 claims = each output poly evaluated at `eval_point` (eq dot product), in the
   order [readset, writeset, rc16num, rc16den, tsnum, tsden, lookupnum, lookupden, initset,
   teardownset] (ZERO for absent OutputTypes).

Reference (this proof): `final_trace_size_log_2 = 4`;
seed after eval-point+batching draws = `0x37fe013de0865662236dfa43310540b6e628ae629be4da583fabaf681c9da480`;
eval_point = [`0515af1d43ebb20064c5512658017079`, `01383e3972ccf84ac8d79d0e5b53a05b`,
`01852fd86551ceb9c7ead07de80d0819`, `002901dac4244987983f17e14a18ca7b`];
batching = `06fe013de0865662236dfa43310540af`.

Fixtures: `whir/testdata/gkr_step1_preimage.hex`, `whir/testdata/gkr_step2_output_evals.hex`.
Rust ref: `capture_gkr_dim_reduce_reference` in large_field.rs. Solidity+forge: `step1_test/`.

## STEP 2b — per dim-reducing layer sumcheck (NEXT; fully mapped)
Layers processed OUTPUT→base: 21 (4 rounds) … 4 (21 rounds), then circuit layers 3..0 (22
rounds). Each layer L (folding_steps = round count):
- initial claim = batched combination of the previous layer's at-point claims via the running
  batching challenge (KernelCollector::compute_combined_claim: RLC over PairwiseProduct /
  LookupPair kernels).
- `folding_steps` sumcheck rounds, each `[E;4]` MONOMIAL `p(X)=c0+c1X+c2X^2+c3X^3`. Verifier
  check per round: `claim == (2*c0+c1+c2+c3) * eq_scale` (existing gkr.sol `sumcheck_rounds`
  already does this — reuse it). Draw `r` (keccak(seed) top-128 mod P after absorbing the 4
  coeffs as BE16), `claim = p(r)`, update `eq_scale` from (z, r).
- THE DELTA vs existing gkr.sol `sumcheck_compress_2pass`: it did `folding_steps-1` rounds +
  an x_last point-check reading 8 output polys at {0,1}. New form does the FULL `folding_steps`
  rounds, then sends `[E;2]` LSB lines per output (10 of them = `final_step_evaluations`),
  absorbs them, and draws 2 challenges `[r_last, next_batching]`. Next-layer at-point claims =
  each output's LSB line interpolated at `r_last`; the running batching challenge becomes
  `next_batching`. (`output_univariate_monomial_form_max_quadratic` in
  prover/src/gkr/sumcheck/mod.rs is the monomial construction; the [E;4] split is
  [x_last=0: v0,v1 | x_last=1: v2,v3], LSB0=(v0,v2), LSB1=(v1,v3), interpolated by r_before_last.)

### STEP 2b — CONVERGED (validated Rust + on-chain)
Rust mirror `verify_dim_reduce_layers` (large_field.rs) verifies all 18 layers of the real
proof: every sumcheck round + every final-step check + boundary permutation. Solidity
`step1_test/GkrDimReduce.sol` (forge `GkrDimReduceTest`, gas 2.19M) reproduces it end-to-end.

- Field is Proth120 with **extension degree 1** → every "E" is a scalar mod P; all arithmetic
  is plain addmod/mulmod. No extension arithmetic anywhere in the GKR verifier.
- Processing order 21→4: `folding_steps = 4,5,…,21` (= `point.len()` at layer entry).
- initial 10 claims = each output column poly at `eval_point` via `eq`. eq bit convention
  (`make_eq_poly_in_full`): eval index bit `n-1-v` ↔ `point[v]` (MSB-first), i.e.
  `eq[j] = Π_v ( bit_{n-1-v}(j) ? point[v] : 1-point[v] )`. Column order = OutputType order =
  logical claim order [readset, writeset, rc16num, rc16den, tsnum, tsden, lookupnum, lookupden,
  initset, teardownset].
- final-step accumulator g (running `batching` powers, one power per emitted value):
  slot0 = l0·l1, slot1 = l0·l1, then 3 lookup pairs each emit num=`v0a·v1b+v0b·v1a` then
  den=`v1a·v1b`, then slot8, slot9 products. Check `g·eq_prefactor == claim`.
- transcript absorbs coeffs/LSB in **sorted-address** order (raw BE16 blob slice); g and the
  next-claim interpolation use **logical** order.
- **Boundary permutation** (circuit-specific, code-gen): only the last processed layer
  (= `num_standard_layers` = 4, folding_steps 21) takes inputs from `global_output_map`, whose
  addresses sort differently. `lsb_logical[i] = lsb_sorted[PERM[i]]`, PERM = [6,7,0,1,2,3,4,5,8,9]
  (PermProduct@{6,7}, Lookup16@{0,1}, LookupTs@{2,3}, Generic@{4,5}, Inits@{8,9}). Cascade
  layers use identity.
- Reference (this proof): after dim-reducing, point.len()=22,
  batching=`0x06616d7d0fe9664e9ad006cc97f250ae`,
  seed=`0xc3616d7d0fe9664e9ad006cc97f250c978fde8d241a2d9d467b73925d8c28fe0`.
- Fixtures: `whir/testdata/gkr_step1_preimage.hex`, `gkr_step2_output_evals.hex`,
  `gkr_dimreduce_data.hex` (20160 B: per layer folding_steps·[c0..c3] then 10·[lsb0,lsb1], BE16).

## STEP 3 — same-sized CIRCUIT layers (layers 3..0, 22 rounds each) — NEXT

Processing order (after dim-reducing): config_idx 3,2,1,0 (`(0..num_standard_layers).rev()`).
Structurally identical to dim-reducing PER LAYER:
  1. `initial_claim = layer_N_compute_claim(prev_claims, batching)` — RLC via a per-layer
     `descs: [(n,o0,o1)]` list (n=0 batch-only skip, n=1 single, n=2 pair). NOT the flat 0..9 RLC.
  2. `verify_sumcheck_rounds` — FULL 22 monomial rounds (SAME loop as dim-reducing; reuse the
     Solidity `GkrDimReduce` round code). Overwrites `state.prev_point` in place (new fold point);
     eq_prefactor uses the PREVIOUS layer's point coord per round.
  3. read `num_dedup_addrs` at-point evals (ONE per input poly — not [E;2] LSB lines).
  4. `g = layer_N_final_step_accumulator(evals, batching, lookup_additive, lookup_alpha,
     perm_linearization_challenges[6], perm_additive, address_high_bits_shift,
     inits_and_teardowns_top_bits)` — the per-gate kernel eval (see below).
  5. `verify_final_step_check`: `g[0]*final_eq == final_claim`.
  6. absorb evals, draw `next_batching`. next `prev_claims` = the at-point evals directly
     (+ `extra_evals` interleaved for cached relations, per a layout map). No interpolation.
  7. `cache_check` (generate_cache_relation_checks) + (layer 0 only) virtual-setup checks
     (range-check-16, range-check-timestamp, inits/teardowns closed-form).

### Per-gate accumulator = flattened descriptors + fixed runtime helpers
The generator (`verifier_generator/src/gkr/standard_layer.rs`) flattens each gate into const
descriptor arrays feeding a SMALL fixed set of runtime evaluators. Port those helpers to Solidity
once; code-gen (parse.rs) only emits the per-gate descriptor data + the accumulate/batch glue.
Runtime helpers (exact math in standard_layer.rs `generate_eval_helpers`):
  - `eval_linear_relation(evals, terms:[(idx,coeff)], constant, j)` = constant + Σ coeff·evals[idx]
  - `eval_vector_lookup(evals, alpha, col_descs:[(col_const,num_terms)], terms, j)` =
    Horner in alpha over columns; each column = col_const + Σ coeff·evals[idx]
  - `eval_max_quadratic(evals, quad_outer:[(a,num_inner)], quad_inner:[(b,coeff)], linear:[(addr,coeff)], constant, j)`
    = constant + Σ_a evals[a]·(Σ_inner coeff·evals[b]) + Σ_lin coeff·evals[addr]  ← the 133 layer-0 gates
  - `eval_memory_expr(evals, challenges, additive, ops:[[usize;6]], j)` — 8 opcodes (ME_OP_*):
    add-base-const, add-eval, add-(1-eval), ch·eval, ch·const, ch·(eval+const), ch·(eval+dyn),
    byte-value-pair (hi·2^8+lo).
  - simple-gate dispatch loop: `SimpleGateType` + `[usize;4]` input indices (covers CopyInBase/Ext,
    grand-products, materialized/cached lookups, mask, trivial product, aggregate rational pair).
  - dual-output lookups (num/den) + inits/teardowns (unique closed form using top_bits).
Coeffs: generator stores `MW::coeff_to_internal_repr` (Montgomery for Blake2s/BabyBear). For
Proth120/Solidity use the PLAIN reduced value (mulmod is direct) — the Solidity FieldWrapper is identity.

### Concrete circuit scope (this circuit, from `inspect_circuit_layer_relations`)
  - layer 0: 153 gates, 16 cached. 92 EnforceSingleMaxQuadraticConstraint + 41 MaxQuadratic (→133
    eval_max_quadratic), 8 LookupPairFromMaterializedBaseInputs, 4 InitialGrandProductFromCaches,
    3 CopyInBaseField, 2 InitsOrTeardownsInitialPair, 2 LookupFromMaterializedBaseInputWithSetup,
    1 LookupWithCachedDensAndSetup. + virtual-setup checks.
  - layer 1: 16 gates, 5 cached. AggregateLookupRationalPair×3, CopyInExtensionField×4,
    LookupPairFromMaterializedVectorInputs×2, LookupUnbalancedPairWithMaterializedBaseInputs×3,
    LookupUnbalancedPairWithMaterializedVectorInputs×1, CopyInBaseField×1, TrivialProduct×2.
  - layer 2: 12 gates. AggregateLookupRationalPair×4, CopyInExtensionField×6, MaskIntoIdentityProduct×2.
  - layer 3: 7 gates (all external). AggregateLookupRationalPair×3, CopyInExtensionField×4.
Suggested build order (smallest first, validate each layer's final-step check in the Rust mirror
before Solidity): layer 3 → 2 → 1 → 0. Layers 2-3 need only {AggregateLookupRationalPair,
CopyInExtensionField, MaskIntoIdentityProduct} — a tractable first slice.

### STEP 3 — Rust mirror CONVERGED (all 4 circuit layers validated)
`verify_dim_reduce_layers` (large_field.rs) now continues past dim-reducing through circuit layers
3→2→1→0 and every initial-claim / sumcheck-round / final-step `g` check passes against the real
proof. Final GKR seed = `0xf3b9657c658435f19389c7cfdd4c772755326af8c4c05a174b582b91bb1fd516`.
Key facts nailed down:
- Handoff dim-reducing→circuit: next-claims = interpolate lsb in **sorted input-address order**
  (the boundary `DIM_REDUCE_INDICES` permutation applies ONLY to `g`, never to next-claims).
- initial claim `compute_claim(descs)`: per gate a (kind,o0,o1): kind0 = max-quadratic constraint
  (advance batch, no claim), kind1 = single output, kind2 = dual lookup (two slots). `output_claims`
  indexed by the layer's sorted output addresses; batch order must match the accumulator.
- final-step evals stored as `Vec<E>` len 1 per input (at-point), keyed+sorted by GKRAddress.
  Transcript: absorb at-point evals (sorted) → draw next_batching → (cached layers) absorb the
  extra cached-relation evals (address-sorted) AFTER the draw. next-claims = merge(at-point, extra)
  address-sorted. address_high_bits_shift = trace_len_log2 + 2 - 16 = 8 here.
- gate `g` kernels (all validated): Copy = b·in; Product/InitialGrandProductFromCaches = b·in0·in1;
  MaskToIdentity = b·((in-1)·mask+1); LookupInitialPair (b+γ,d+γ)→num=bg+dg,den=bg·dg;
  LookupWithSetup num=dg−setup0·bg,den=bg·dg; LookupUnbalanced num=a·(r+γ)+b,den=b·(r+γ);
  LookupAggregatePair num=a·d+c·b,den=b·d; LookupCachedDens num=a·(d+γ)−c·(b+γ),den=(b+γ)(d+γ);
  eval_max_quadratic = const+Σ_a ev[a]·(Σ coeff·ev[b])+Σ coeff·ev[addr]; InitsOrTeardownsInitialPair
  = lhs·rhs, each side = perm_additive + 1 + lin[0]·setup_lo + lin[1]·(setup_hi+topbits[set]<<shift)
  (+ teardown: lin[2..6]·ts/value mem cols). γ=lookup_additive=ch[8]; lin=ch[0..6]; perm_add=ch[6].
- Cache-relation consistency checks — MIRRORED + validated. After merging next-claims, each cached
  (virtual) poly's at-point eval must equal the combination of its dependency at-point evals, indexed
  in target_addrs (= merged address-sorted) order:
    · SingleColumnLookup: expected = constant + Σ coeff·claim[dep]
    · VectorizedLookup: expected = Σ_col α^col·(col_constant + Σ coeff·claim[dep])   (α = lookup_alpha = ch[7])
    · VectorizedLookupSetup: expected = Σ_dep α^dep·claim[dep]
    · MemoryTuple: cached poly must equal its memory expression built from memory-column at-point
      evals + permutation challenges (SAME math as eval_memory_expr):
        expected = perm_additive
                 + address_space {Constant c | IsRam→mem[off] | IsRegister→(1−mem[off])}
                 + lin[ADDR_LOW]·addr_low (+ lin[ADDR_HIGH]·addr_high for U32/indirect)
                 + lin[TS_LOW]·(mem[ts0]+ts_offset) + lin[TS_HIGH]·mem[ts1]        (if Normal)
                 + lin[VAL_LOW]·val_low + lin[VAL_HIGH]·val_high                    (U16Limbs; U8Limbs
                   combines hi·2^8+lo per half). lin = ch[0..6], perm_additive = ch[6].
  This proof: layer 1 = 5/5, layer 0 = 16/16 (incl. 8 MemoryTuple). Purely a check — transcript-neutral.

  The MemoryTuple check is REQUIRED: this circuit has 4 `InitialGrandProductFromCaches` gates
  (layer 0) that consume the cached memory tuples as opaque `Product(cached_a, cached_b)` inputs, so
  without it the memory grand-product is not tied to the memory columns. The Solidity verifier takes
  its implementation from the prover's logic (debug_utils::evaluate_memory_tuple_from_claims), which
  the Rust mirror already reproduces. (An old gap in verifier_generator's MemoryTuple arm was fixed
  on a separate branch; not relevant here since the Solidity path is prover-based, not generator-based.)
- Layer-0 virtual-setup closed-form checks — MIRRORED + validated (4/4). At the layer-0 folding
  point `pt` (= new_point, n=22), each VirtualSetup poly's sent at-point eval must match a closed form:
    · range-check (bits=16 for RangeCheck16Bits, 19 for RangeCheckTimestamp):
      (Σ_{k<bits} 2^k·pt[n-1-k]) · Π_{k=bits..n} (1 − pt[n-1-k])
    · inits/teardowns (word_bits=2 ⇒ take_count=14):
      low = Σ_{k<take_count} 2^{word_bits+k}·pt[n-1-k];  high = Σ_{k<n-take_count} 2^k·pt[n-1-take_count-k]
  VirtualSetup at-point evals looked up by ADDRESS in the merged claims. Transcript-neutral.

### GKR verifier is now COMPLETE in Rust
transcript → entry → 18 dim-reducing → 4 circuit layers → cache-relation checks → virtual-setup
checks all pass vs the real proof. Only the WHIR PCS opening remains (base-layer memory/witness/setup
claims from layer 0 at the final 22-coord point; existing whir.sol).
- Base-layer at-point evals from layer 0 (BaseLayerMemory/Witness/Setup at the final 22-coord point)
  are the claims WHIR must open.

Then WHIR PCS opening (existing whir.sol) closes out the multilinear evaluation at the final 22-coord
point, and stateless gkr.sol calls the 3rd-party `mark_gkr_verified(bytes32)`.

---

## STEP 3 SOLIDITY GENERATOR — implementation plan (parse.rs → circuit.yul + gkr.sol)

The generated Yul must stay as gas-efficient as the existing `gkr.sol`/`circuit.yul`
(hand-scheduled Yul, static heap via `*_PTR()`, non-canonical arithmetic funneled through
`mulmod`, `mod(add())` over `addmod`, inline exprs to cut stack pressure — see HEURISTICS.md).
The Rust mirror `verify_dim_reduce_layers` is the validated authority for every kernel.

### Current state of the draft (as found)
- `parse.rs` is a WORKING gas-efficient generator for a SIBLING circuit (BabyBear, no-caches,
  2^24) but: (a) does NOT compile — mid-refactor left `lookrelsingle_to_calldata` and siblings
  declared `-> String` while returning `Dual`, and callers use `{:x}` (Yul) on Strings (errors at
  ~L600/604/816/877/916 of the original); (b) the input-address resolver `gkraddress_to_calldata`
  is commented out except `Setup` + `todo!()`; (c) targets the old field.
- `gkr.sol` skeleton uses `P = 2^128-159`, `GKR_CIRCUIT_LAYER_ROUNDS = 24`, static heap
  (`MEMORY_CHALLS_PTR`, `LOGUP_CHALLS_PTR`, `POINT_PTR`, `GKR_CIRCUIT_CACHE_PTR`, …), and the
  circuit.yul is injected at `// __INLINE_CIRCUIT_YUL__` by parse.sh.
- circuit.yul already provides the right STYLE: `sumcheck_circuit_layer{0..3}`, `gkr_memrel_compress`
  / `gkr_memrel_compress_high`, `gkr_lookrel_compress_half`, `gate_aggregatelookuprationalpair`,
  `pointcheck_update`/`logup_pointcheck_update`, `gkr_virtual_poly_*`, `sumcheck_rounds_circuit`.

### DONE this pass
- `proth120_const_to_evm(&Proth120) -> Dual` added to parse.rs: small pos → literal; small neg
  (near P) → `sub(P, n)`; else full `0x..` u128 literal. (This circuit's coeffs are near 2^120 =
  one uint128; funnel through mulmod.)

### Increments to execute (each validated against the Rust mirror's per-layer g)
1. Fix the mid-refactor compile: make the `*_to_calldata*` helpers return `Dual` consistently
   (they already build Dual); update signatures/callers. Get parse.rs building on the OLD target.
2. Field migration: switch `GKRCircuitArtifact<BabyBearField>` → `<Proth120>`, target
   `unified_reduced_machine_layout_gkr_proth120.json`, replace `const_to_evm(&x.as_u32_reduced())`
   call sites with `proth120_const_to_evm(x)`, set trace_len assert to 1<<22.
3. Complete the input-address resolver (the crux): map each layer input GKRAddress to its source.
   Calldata layout = per-layer at-point evals in SORTED input-address order, 16B BE each
   (= mirror's `evals` = final_step_evaluations.values()); read as `shr(128, calldataload(add(ptr,
   mul(16, idx))))`. Cached/virtual/extra values live on the static heap (`GKR_CIRCUIT_CACHE_PTR`
   slots) via mstore/mload, matching the merged-claims address order. Resolve BaseLayerMemory/
   Witness/Setup/InnerLayer/Cached/VirtualSetup → calldata idx or heap slot.
4. With-caches relation handling (the mirror's kernels are the spec):
   - point-check accumulator per layer = `circuit_layer_g`: Copy, Product/InitialGrandProductFromCaches,
     MaskToIdentity, LookupInitialPair, LookupWithSetup, LookupUnbalanced, LookupAggregatePair,
     LookupCachedDens, eval_max_quadratic (const+Σ a·(Σ coeff·b)+Σ coeff·lin), InitsOrTeardownsInitialPair.
   - initial claim = compute_claim(descs) RLC (kind 0/1/2).
   - cache-relation checks: SingleColumnLookup / VectorizedLookup / VectorizedLookupSetup (linear),
     and MemoryTuple (gkr_memrel_compress — REQUIRED here, prover-based; see MemoryTuple note above).
   - layer-0 virtual-setup closed-form checks (range-check-16/timestamp, inits/teardowns low/high).
5. gkr.sol migration: `P` → Proth120, rounds 24→22, port the validated keccak transcript from
   `step1_test/GkrStep1.sol` (transcript init + entry) and the dim-reducing verifier from
   `step1_test/GkrDimReduce.sol` (already on-chain-validated) into the hand-written skeleton; wire
   the 22-coord handoff into `sumcheck_circuit_layer*`; stateless entry calling `mark_gkr_verified`.
6. Validate: parse.sh builds; forge-check the full gkr.sol against the real proof calldata; compare
   the post-GKR seed to `0xf3b9657c…` and gas vs the existing hand-written baseline.

---

## STEP 4 — GKR→WHIR handoff (claims merge + batching + batched opening) + calldata + stub

Extracted from prover/src/gkr/prover/mod.rs (lines 864-1010, merge_claims @1057). Sequence AFTER the
circuit layers finish (base-layer claims + point z at 22 coords, seed = post-GKR 0xf3b9657c…):

1. **base-layer claims by group**: from the layer-0 merged next-claims, take
   mem_polys_claims = claims[BaseLayerMemory(0..num_mem)] in column order, wit = BaseLayerWitness(..),
   setup = Setup(..). (VirtualSetup/Cached are NOT opened by WHIR — they were consumed/derived in-layer.)
2. **draw extra_coordinates** = `draw_random_field_els(seed, pack_log2)` (pack_log2=4 → 4 field els),
   drawn RIGHT HERE (no absorb first; all prover vars already in transcript).
3. **merge (packed)**: merged = mem ++ wit; then `merge_claims(merged, extra)` and
   `merge_claims(setup, extra)` independently. merge_claims: for each chunk of 2^pack_log2 (16) claims
   (zero-padded to 16), fold with the extra-coords **in reverse**: each round pairs (a,b)→
   interpolate_linear(a,b,r) = a+(b-a)·r, halving; after 4 rounds → 1 merged claim per 16-chunk.
4. **extend point**: base_layer_z = extra_coordinates (PREPENDED) || old base_layer_z → 26 coords
   (trace_len_log2_for_whir = 22+4 = 26).
5. **draw whir_batching_challenge**: `draw_random_field_els_with_pow(seed, 1, batched_proximity_pow_bits)`
   → 1 el (+ PoW nonce = proof.batched_proximity_check_pow_nonce, validate against it).
6. **batched opening value**: whir_fold batches the merged columns with whir_batching_challenge:
   batched_claim = Σ_i claim_i · batching^i over (mem_merged ++ wit_merged(empty) ++ setup_merged)
   [confirm exact order/inclusion of setup from whir_fold before finalizing]. This is the single value
   WHIR opens = the batched multilinear evaluated at base_layer_z (26 coords).
7. **WHIR call stub** (post-verification handoff): pass (base_layer_z[26], batched_claim,
   whir_batching_challenge, seed, caps) to the WHIR verifier (existing whir.sol). gkr.sol's stub should
   marshal exactly these; then WHIR verifies the opening and, on success, calls mark_gkr_verified(bytes32).

**Calldata serializer (Rust, real proof → bytes)**: emit, in gkr.sol stream order — (a) transcript
preimage (520 B, already have gkr_step1_preimage.hex); (b) output evals (2560 B, gkr_step2_output_evals.hex);
(c) dim-reducing blob (20160 B, gkr_dimreduce_data.hex); (d) per circuit-layer: 22 rounds·[c0..c3] (BE16)
then num_dedup_addrs at-point evals (BE16) in group-offset order + extra cache evals; (e) WHIR proof bytes.
Validate end-to-end: gkr.sol run reproduces post-GKR seed 0xf3b9657c then the merge/batching draws.

### STEP 4 — VALIDATED (Rust mirror, real proof)
`verify_dim_reduce_layers` now continues through the GKR→WHIR handoff; the WHIR-batching PoW nonce
matches `proof.batched_proximity_check_pow_nonce` (=0), which validates the whole handoff transcript
(post-GKR seed → 4 extra-coord draws → merge → batching draw). Reference values (this proof):
- pack_log2 = 4; base_layer_z = 22 coords → whir_point = 26 coords (extra || base_layer_z).
- merge: mem+wit = 106 claims → 7 merged (chunks of 16); setup = 10 → 1 merged.
- whir_batching PoW bits = 0, nonce = 0; whir_batching_challenge = 0x01addc07bd97a7c45d787afb1a7f1554.
- batched_opening_value (= Σ claim_i·batching^i over merged_mem_wit ++ merged_setup)
  = 0x05fdc775c0b884f0e6825acb6af3c30f.
- seed after batching draw = 0xbeaddc07bd97a7c45d787afb1a7f156f875c4404e6b40825549d95c7c3e964ae.
WHIR-stub inputs = (whir_point[26], batched_opening_value, whir_batching_challenge, seed, caps).
Order caveat still to confirm from whir_fold: whether setup claims are appended after mem+wit in the
batching sum (assumed yes here) and the exact per-column batching-power indexing.

# Appendix — Protocol algorithms and soundness

```text
FullStatement
  ├─ VisitChunks → Chunk → GKR layers → OutputChecks → WHIR
  ├─ CloseMemory → equal event multisets → machine execution
  └─ FinishChain → (application result, program-history digest)
Recursive step: prove the execution of FullStatement; repeat.
```

**Shared soundness convention.** Field arithmetic uses E, BabyBear's quartic extension, with base modulus p = 2013265921. Under independent sampling, μ bounds each E-valued challenge's maximum point probability; a nonzero polynomial of total degree d vanishes with probability ≤ dμ. For four independent uniform 32-bit words reduced modulo p, μ ≤ (3/2³²)⁴ = 81/2¹²⁸ ≈ 2^(−121.66). Fiat–Shamir accounting is in Algorithm 12.

---

> **Algorithm 1 — FullStatement**
>
> **Public statement:** program setup ProgramCaps, final state z = ((vⱼ,τⱼ,lo,τⱼ,hi)ⱼ₌₀³¹, pc,τlo,τhi), selected verifier/profile. **Witness:** execution columns, IT data, lookup multiplicities and all chunk proofs. **Output:** (y,h), eight words each.
>
> **Notation:** `ProgramCaps` lists program setup caps in family order; each cap contains sixteen eight-word hashes. `Block(…)` zero-pads to sixteen words. RS,WS are read/write product accumulators; IT is RAM initialization/teardown.
>
> ```text
> Prover preparation:
>   Generate the chunks and z; commit all memory columns before χ.
>   In the merged feeder, commit memory and witness columns together.
>   Form the global transcript in exactly the order reconstructed below;
>   solve its 19-bit PoW; derive χ = (χ₀,…,χ₅,η) ∈ E⁷.
>   Build the remaining witness columns; prove each Chunk with this χ.
>
> Verifier / proof-stream order:
> 1. Read ProgramCaps and the 32 final register triples; require v₀ = 0.
>    T ← empty global transcript; absorb the 96 register words.
>    Read pc,τlo,τhi; absorb Block(pc,τlo,τhi).
> 2. Read supplied χ. Set RS ← 1; WS ← 1; cycles ← 0.
> 3. VisitChunks(ProgramCaps,χ), updating T,RS,WS,cycles and the element count.
> 4. Finalize T; read a low/high-word nonce; check 19-bit PoW.
>    Derive χ′ ∈ E⁷ from the resulting seed; require χ′ = χ.
> 5. CloseMemory(z,χ,RS,WS); return FinishChain(ProgramCaps,z,mode).
> ```
>
> **Soundness — composition (adapted).** Chunk relations and CloseMemory establish execution under the reconstruction lemmas in Algorithm 9. The deferred χ check requires the absorbed caps, windows and boundary data to fix every memory factor before χ. Counts are not separately absorbed; setup and separate witness caps enter local transcripts. Required binding lemma: this encoding fixes the participating event collection.

---

> **Algorithm 2 — VisitChunks**
>
> **Input/state:** ProgramCaps,χ,T,RS,WS,cycles; fixed family/delegation order.
>
> **Notation:** o is a verified chunk's output; `Acc(o)` multiplies RS,WS by its ordinary read/write products. `DelegationCaps[d]` is the fixed setup cap for delegation d; IT is RAM initialization/teardown.
>
> ```text
> Unrolled:
>   for each configured instruction family f:
>     read n_f; if n_f > 0: absorb Block(f)
>     repeat n_f times:
>       cycles ← cycles + 2^trace_log₂(f); require cycles < 2³⁶
>       o ← Chunk(f,χ); require o.setup_caps = ProgramCaps[f]
>       absorb o.memory_caps; Acc(o)
>   read n_IT; require 1 ≤ n_IT ≤ 8; previous ← −1
>   absorb Block(IT family)
>   repeat n_IT times:
>     o ← Chunk(IT,χ)
>     for b in o's eight windows: require previous < b < 64; previous ← b
>     absorb o.memory_caps, then Block(o.windows); Acc(o)
>
> Unified:
>   read n,n_IT; require n > 0 and 1 ≤ n_IT ≤ n; previous ← −1
>   for i = 0,…,n−1:
>     cycles ← cycles + 2²⁴; require cycles < 2³⁶
>     o ← Chunk(unified,χ); require o.setup_caps = ProgramCaps[0]
>     absorb Block(unified family,o.windows), then o.memory_caps; Acc(o)
>     if i < n−n_IT: require both window identifiers = 0
>     else:
>       require o's separate IT product pair; multiply it into RS,WS
>       for b in o's two windows: require previous < b < 64; previous ← b
>
> Both:
>   elements ← 4·cycles
>   for each configured delegation type d:
>     read n_d; if n_d > 0: absorb Block(d)
>     repeat n_d times:
>       o ← Chunk(d,χ); require o.setup_caps = DelegationCaps[d]
>       absorb o.memory_caps; Acc(o); elements ← elements + A_d
>   require elements < 2⁴⁰
> ```
>
> **Instantiation.** Unrolled base order: add/sub/LUI/AUIPC/MOP; jump/branch/compare; shift/binary; unsigned multiply/divide; word memory; subword memory. Continuation omits multiply/divide and subword memory. Trace logarithms are 24 except multiply/divide, which uses 23. Delegation order and charges A_d: BLAKE2s 44·2²⁰; bigint 20·2²²; Keccak special5 15·2²²; theta/rho 17·2²²; column parity 15·2²²; chi5 13·2²². Standalone IT covers eight windows of 2²⁴ words per proof. Unified uses 2²³-row circuits but charges 2²⁴ cycles per proof; its two windows each cover 2²⁵ bytes. With b < 64, this unified configuration covers windows below 2³¹ bytes; unrolled covers the 2³²-byte range.
>
> **Soundness — participant/window binding (new).** Setup checks fix program/precompile tables. Strictly increasing, circuit-bound windows prevent repeated RAM initialization/teardown; leading unified IT products are excluded. Requires the capacity charges to bound the compiled event counts.

---

> **Algorithm 3 — Chunk**
>
> **Public input:** C,χ, caps and window identifiers b. **Witness:** M,W,S, lookup multiplicities and intermediate gate values. **Relation:** C's gates/zero constraints and selected lookup memberships hold; exported products equal the selected memory-event products. **Output:** products, MemoryCaps,SetupCaps,b.
>
> **Notation:** C is the compiled circuit on 2ⁿ rows, fixing gates, zero constraints, column order, tables and proof schedule. M,W,S are memory, remaining witness and setup columns, committed by MemoryCaps,WitnessCaps,SetupCaps. P,V denote prover/verifier; MLE(A) is table A's multilinear extension.
>
> ```text
> 1. P → V: b,SetupCaps,MemoryCaps,WitnessCaps, omitting absent commitment groups.
>    P has fixed W, including multiplicities, before this step completes.
>    V: initialize local T with the single message
>         b ∥ χ ∥ SetupCaps ∥ MemoryCaps ∥ WitnessCaps;
>       omit absent groups and alignment padding from its length.
> 2. P → V: lookup-PoW nonce. V: check it; draw (α,β) ∈ E².
>    Read/hash this nonce even when its configured bit count is zero.
> 3. P: evaluate C forward, then accumulate outputs to sixteen entries.
>    P → V: sixteen-entry tables A₀,…,Aₛ₋₁.
>    V: commit them; draw (u₀,…,u₃,λ); aⱼ ← MLE(Aⱼ)(u).
> 4. For k = 4,…,n−1: GKRLayer(compression,k).
>    For each main layer, outputs towards inputs: GKRLayer(main,n).
>    Obtain base-column claims fⱼ(ζ) = aⱼ.
> 5. P → V: batching/proximity-PoW nonce. V: check it; draw γ ∈ E.
> 6. products ← OutputChecks(A₀,…,Aₛ₋₁).
> 7. WHIR(base caps,ζ,a,γ,T); return products,MemoryCaps,SetupCaps,b.
> ```
>
> **Variants.** Standalone IT has only MemoryCaps; the merged feeder has SetupCaps and one cap for M ∥ W. Ordinary chunks have all three groups. WHIR continues the GKR transcript. These BabyBear instances are unpacked. Packed instances draw fresh pack coordinates after the main layers, merge claims within each commitment set by multilinear weights, and append the coordinates to ζ before the batching PoW.
>
> **Soundness — local reduction (adapted).** GKR reduces output-table claims to base openings established by WHIR. Queries, selectors and multiplicities must be fixed before α,β. Product/lookup compression is included in ε_GKR.

---

> **Algorithm 4 — EQSumcheck**
>
> **Input:** incoming point u ∈ Eᵏ and batched claim v for gate polynomial G, of individual degree ≤ 2. **Output:** point r, scalar v, last EQ factor e.
>
> **Notation:** eq(u,x) = ∏ⱼ((1−uⱼ)(1−xⱼ)+uⱼxⱼ), the Boolean-cube interpolation kernel.
>
> ```text
> e ← 1
> for j = 0,…,k−1:
>   P → V: coefficients of gⱼ(X), degree ≤ 3
>   V: require e·(gⱼ(0)+gⱼ(1)) = v; commit gⱼ; rⱼ ← Draw(T)
>      v ← gⱼ(rⱼ); e ← (1−rⱼ)(1−uⱼ)+rⱼuⱼ
> return (r,v,e)                 // e is replaced, not accumulated
> ```
>
> Honest gⱼ(X) = eq(uⱼ,X)·Σ_{x′∈{0,1}^(k−j−1)} eq(u_{>j},x′)·G(r_{<j},X,x′). The caller closes with v = e·G(r).
>
> **Soundness — Sumcheck (standard), EQ factoring (adapted).** Conditional on e ≠ 0, each false cubic identity survives with probability ≤ 3μ. The new factor is 1−uⱼ+(2uⱼ−1)rⱼ: it is 1/2 when uⱼ = 1/2, otherwise it has one root, costing ≤ μ. Thus k rounds cost ≤ (3k+Z)μ with Z ≤ k charged EQ-zero events, provided the final gate evaluation is established downstream.

---

> **Algorithm 5 — GKRLayer**
>
> **Input:** output claims (u,a), batching challenge λ and compiled layer C.
>
> **Notation:** `Batch` uses C's power order in λ and includes claim 0 for every zero constraint. `Gate` is the same batched gate expression, evaluated by V.
>
> ```text
> 1. v ← Batch(a and zero claims; λ); (r,v,e) ← EQSumcheck(u,v).
> 2. If compression:
>      P → V: hⱼ(0,r),hⱼ(1,r) for all required inputs
>      V: require v = e·Gate(endpoint values;λ); commit all endpoints
>         draw (t,λ′); a′ⱼ ← (1−t)hⱼ(0,r)+t·hⱼ(1,r)
>      return ((t,r),a′,λ′)
>    Otherwise, main layer:
>      P → V: required input evaluations at r
>      V: require v = e·Gate(input values;λ)
>      P → V: additional cached-relation evaluations required by C
>      V: commit input/cache evaluations together; draw λ′
>         check C's cache relations and virtual setup evaluations
>      return preceding-layer claims at r in C's address order, and λ′
> ```
>
> Compression gates: product h₀h₁; rational sum (n₀d₁+n₁d₀, d₀d₁). V evaluates virtual setup polynomials directly; committed setup polynomials become WHIR opening claims.
>
> **Soundness — GKR (adapted).** An initial false sixteen-entry table test costs ≤ (4+b−1)μ for b tables; each further power batch of b fixed claims costs ≤ (b−1)μ. Endpoint interpolation adds a degree-one test for fixed endpoint discrepancies. For L main layers, R = Σ_{k=4}^{n−1}k + Ln cubic messages. Then ε_GKR ≤ min(1, μ(4+B+3R+Z+S)), Z ≤ R, where B counts batching degrees and S the remaining point/line tests. Requires the compiled gate/cache/virtual-setup induction and instantiated B,S counts.

---

> **Algorithm 6 — OutputChecks: memory products and LogUp**
>
> **Input:** original sixteen-entry tables.
>
> **Notation:** Q is the query multiset and T the lookup table; mₜ is table tuple t's committed multiplicity. Tuples have width w, including any table identifier. With lookup challenges α,β, define ℓ(t) = β + Σ_{j=0}^{w−1} αʲtⱼ.
>
> ```text
> 1. For each ordinary or embedded-IT product pair (A_R,A_W):
>      R ← ∏ⱼ₌₀¹⁵ A_R[j]; W ← ∏ⱼ₌₀¹⁵ A_W[j].
> 2. For each present lookup pair (A_N,A_D):
>      N ← 0; D ← 1
>      for j = 0,…,15:
>        (N,D) ← (N·A_D[j]+A_N[j]·D, D·A_D[j])   // simultaneous
>      require N = 0 and D ≠ 0
> 3. Return the product pairs.
> ```
>
> The leaf relation is Σ_{q∈Q} 1/ℓ(q) = Σ_{t∈T} mₜ/ℓ(t). Its rational compression tree is proved by GKR with base openings in WHIR. The 16-bit and timestamp virtual tables have 2¹⁶ and 2¹⁹ entries. IT has zero categories; BLAKE and Keccak have two; the other listed circuits have three. The compiled circuit determines selectors and padding queries.
>
> **Soundness — LogUp (standard), encodings/counts (adapted).** For nonzero denominators and fixed tuples/multiplicities, a false rational identity gives a nonzero polynomial after clearing denominators. Thus ε_lookup ≤ μΣₐDₐ, with Dₐ ≤ Tₐ·max(1,wₐ) for Tₐ fraction occurrences in category a. Membership requires invalid-tuple query counts to be nonzero modulo p; fewer than p query occurrences per category suffices. Requires per-circuit occurrence bounds; field-valued multiplicities do not themselves bound integer counts. The union bound applies with shared α,β.

---

> **Algorithm 7 — WHIR**
>
> **Input:** base caps; claims fⱼ(ζ) = aⱼ; γ; continued T; round folds kᵣ, queries tᵣ, PoW bits bᵣ, fixed Reed–Solomon domains and tree layouts. **Witness:** base and folded polynomials and authenticated leaves. **Relation:** the committed base polynomials have the claimed evaluations and required encoding/degree bounds.
>
> **Notation:** fⱼ are column MLEs and ζ their opening point. For monomial coefficients cₜ, F_f(X) = Σₜ cₜXᵗ and powers(s) = (s,s²,s⁴,…), so F_f(s) = f(powers(s)); low-index bits select the first folded variables. eq is the interpolation kernel from EQSumcheck; w is the running weight function.
>
> ```text
> 1. P: f ← Σⱼ γʲfⱼ. V: v ← Σⱼ γʲaⱼ; w(x) ← eq(ζ,x).
>    Invariant: v = Σ_{x∈{0,1}^remaining_dimension} f(x)w(x).
>    old_caps ← base caps in memory/witness/setup order.
> 2. For each nonfinal round r:
>      Run kᵣ QuadraticSteps, obtaining fold challenges a.
>      P: f_next ← f                  // already restricted by those steps
>      P → V: cap next_caps committing to the proposed f_next
>      V: commit next_caps; ξ ← Draw(T)
>      P → V: u claimed as F_next(ξ)
>      V: commit u; read/check bᵣ-bit PoW; draw tᵣ query indices
>         with replacement; δ ← FreshDraw(T)
>      For each query j:
>        P → V: old-oracle leaves and Merkle paths
>        V: authenticate at configured tree positions; qⱼ ← Fold(leaves,a)
>           sⱼ ← (ω^query_index[j])^(2^kᵣ), ω the old-domain generator
>      V: w ← w + δ·eq(powers(ξ),·) + Σⱼ δ^(j+2)·eq(powers(sⱼ),·)
>         v ← v + δ·u + Σⱼ δ^(j+2)·qⱼ
>      P: f ← f_next. V: old_caps ← next_caps.
> 3. Run the final kᵣ QuadraticSteps.
>    P → V: monomial coefficients c of the remaining polynomial.
>    V: commit c; read/check final PoW; draw final query indices.
>       Authenticate/fold old leaves, defining sⱼ as in step 2;
>       require each qⱼ = Σₗ cₗsⱼˡ.
>       Reconstruct f_final from c; require v = Σₓ f_final(x)w(x).
> 4. Accept the base-opening claims.
> ```
>
> The same fold challenges restrict f,w and the old-oracle leaves. In the first round authenticate every nonempty base oracle and batch its leaf columns with the claims' γ powers; later rounds have one old oracle. Merkle paths are checked but not absorbed. Query evaluations enter the running claim on f_next. For m remaining variables, deg(F_f) < 2^m; the schedule fixes Reed–Solomon domain size and LDE.
>
> **Soundness — WHIR (adapted).** Assume binding caps and a proximity/list-decoding bound for the coefficient leaves, accumulator and capacity-based schedule. For c columns, batching costs ≤ (c−1)μ; each quadratic step ≤ 2μ; each δ combination ≤ (tᵣ+1)μ; a fixed false degree-d OOD equality ≤ dμ. A fixed candidate with agreement fraction a survives t independent queries with probability ≤ aᵗ. Requires agreement and candidate-list bounds for every round. Using disjoint error terms, ε_PCS ≤ ε_batch + ε_proximity/list + ε_OOD + ε_query + ε_combine + ε_quadratic + ε_binding.

---

> **Algorithm 8 — QuadraticStep and Fold**
>
> **Input:** running claim v, current f,w; authenticated leaf data with configured encoding.
>
> **Notation:** a = (a₀,…,aₖ₋₁) are fold challenges; leaf[b] indexes local monomial coefficients. x is a nonzero coset point; F_f is the univariate encoding of f. The κ values are folded EQ weights for stored evaluation constraints.
>
> ```text
> QuadraticStep:
>   P → V: three coefficients of h(X) = Σ_x f(X,x)w(X,x), degree ≤ 2
>   V: require h(0)+h(1) = v; commit h; a ← Draw(T)
>   P: f ← f(a,·). V: v ← h(a); w ← w(a,·). Return a.
>
> Fold, coefficient leaves:
>   return Σ_{b∈{0,1}ᵏ} leaf[b]·∏ⱼaⱼ^bⱼ
>
> Fold, evaluation leaves:
>   for each aⱼ, pair A = F_f(x), B = F_f(−x) in configured coset order
>   replace by (A+B+aⱼ·(A−B)/x)/2; square coset points; repeat
>   return the remaining value
> ```
>
> **Soundness — Sumcheck (standard), encoding map (adapted).** Requires the coset/bit-reversal map to match the leaf encoding. Coefficient leaves contain local monomial tensors. Store the weight as folded EQ prefactors; at every later fold, square each stored OOD/query scalar. The final cube sum is κ₀f_final(ζ_remaining) + ΣⱼκⱼF_final(sⱼ), using the updated OOD/query scalars.

---

> **Algorithm 9 — CloseMemory**
>
> **Input:** final state z,χ, authenticated products RS,WS.
>
> **Notation:** R,W are read/write event multisets; χ = (χ₀,…,χ₅,η). In event t = (a,t₀,…,t₅), the limbs are address lo/hi, timestamp lo/hi, value lo/hi; tags are 0 = register, 1 = RAM, 2 = PC. Define Lχ(t) = a + η + Σⱼ₌₀⁵χⱼtⱼ with six independent coefficients.
>
> ```text
> 1. Initial ← ordinary-register writes x0,…,x31 of value 0 at time 0,
>              and the PC write (value 0, time 4).
>    Final ← the 32 register reads and PC read specified by z.
> 2. WS ← WS·∏_{t∈Initial} Lχ(t); RS ← RS·∏_{t∈Final} Lχ(t).
>    Require RS = WS. RAM boundaries already enter through IT products.
> ```
>
> **Soundness — fingerprint (standard), event encoding (adapted).** Assume R,W are fixed before χ and their encoding is injective. Unequal multisets give a nonzero difference of products: each affine factor has η-coefficient 1, so unique factorization distinguishes multisets. Hence ε_mem ≤ Nμ, N = max(|R|,|W|), once per statement. The boundary helper splits values into 16-bit limbs but reduces timestamp words modulo p without a 19-bit check; requires injectivity on accepted boundary data.
>
> **Soundness — execution reconstruction (adapted/new).** Required reconstruction lemma: equal events, local relations and authenticated setups imply an execution from (pc,time) = (0,4) and zero ordinary registers/RAM to z. Its premises include initialization/IT coverage, strict timestamp growth, PC connectivity, decoder membership, delegation matching, inactive-row neutrality and range propagation.

---

> **Algorithm 10 — FinishChain**
>
> **Input:** program setups ProgramCaps, final state z, base/continuation mode. **Output:** (y,h).
>
> **Notation:** ProgramCaps is the ordered list of program setup caps; vⱼ and pc are final register values and PC from z. `Block(…)` zero-pads to sixteen words.
>
> ```text
> 1. y ← (v₁₀,…,v₁₇); e ← Hash(Block(pc),ProgramCaps[0],…,ProgramCaps[last]).
>    Block(pc) has zero timestamp slots.
> 2. If base:
>      require (v₁₈,…,v₂₅) = 0⁸; h ← Hash(0⁸ ∥ e).
>    Otherwise:
>      h_in ← (v₁₈,…,v₂₅)
>      read sixteen-word preimage (h_prev,e_prev)
>      require Hash(h_prev ∥ e_prev) = h_in
>      if e_prev = e: h ← h_in
>      else:          h ← Hash(h_in ∥ e)
> 3. Return (y,h).
> ```
>
> **Soundness — program-history binding (new).** Under hash binding and authenticated verifier executions, h commits to the sequence of setup/ending-PC identities with consecutive repetitions collapsed. Terminal acceptance checks the expected chain and successful ending PC; depth/work requires an external bound.

---

> **Algorithm 11 — Recursion and terminal acceptance**
>
> **Public claim:** application identity, expected collapsed verifier history and result y. **Witness:** child proof bundle and its verifier-execution trace. **Recursive relation:** the selected verifier program runs FullStatement on the child and reaches its successful return with (y,h) in x10,…,x25.
>
> ```text
> 1. Prove the application execution with unrolled circuits;
>    verify using fsv_unrolled_base_layer_sec_100.
> 2. Prove that verifier's execution with unrolled circuits;
>    verify using fsv_unrolled_recursion_layer_sec_100; repeat as needed.
> 3. Bridge: prove an unrolled verifier's execution with unified circuits.
>    The output is a unified bundle for the same child-verification task.
> 4. Verify unified bundles using fsv_unified_recursion_layer_sec_100;
>    prove those verifier executions with unified circuits; repeat.
> 5. Terminal caller: verify the last proof, authenticate its current
>    setup/program identity and successful ending PC, check the expected
>    collapsed chain h, and expose y as the application result.
> ```
>
> Direct-entry binaries read ProgramCaps first. Library dispatchers prepend an op word: 1/2 selects unrolled base/continuation, or unrolled/unified continuation in the other dispatcher. The L1 route uses a merged-commitment feeder, then a packed Proth120 proof with a Keccak transcript. Its serialization, public claim, contract linkage and acceptance predicates require a separate protocol.
>
> **Soundness — recursive composition (adapted).** Outer execution soundness and authenticated verifier identity/success imply child acceptance. Induction requires these conditions at every handoff and an external depth/work bound; Algorithm 12 sums errors over the proved invocations.

---

> **Algorithm 12 — Transcript draws and composed error**
>
> **Parameters:** seven-round BLAKE2s; global buffering transcript; local chaining transcript; bounded adversarial hash work.
>
> **Notation:** b is the PoW bit count; H bounds eligible hash trials; ε is the conditional algebraic failure probability at one gate.
>
> ```text
> Global absorption: buffer the specified messages; hash on finalization.
> Local Commit(m): hash m using the previous seed as the chaining value.
> Draw: start with current seed words; hash forward for additional blocks.
> FreshDraw: hash forward first, then consume words.
> Extension challenge: four words reduced modulo p form the E coordinates.
> PoW_b: read two-word nonce; hash (seed ∥ nonce) as a fresh message;
>        require the configured b zero bits in the first digest word;
>        replace seed; subsequent draws skip that first word.
>
> Conditional algebraic budget per statement:
>   ε_stmt ≤ ε_mem + Σ_chunks(ε_lookup + ε_GKR + ε_PCS).
> Conditional budget over d proved statement invocations:
>   ε_alg,total ≤ Σ_{ℓ=1}^d ε_stmt,ℓ + ε_chain + ε_terminal.
> ```
>
> **Soundness — root bounds (standard), Fiat–Shamir/PoW (new).** For one fixed false claim and an idealized hash trial with independent gate/challenge bits, Pr[gate passes and bad challenge] ≤ 2^(−b)ε. Over H eligible trials, the bound is min(1,H·2^(−b)ε). Apply this per gated challenge, accounting for adaptive prefixes, shared digests and all eligible trials. Requires a Fiat–Shamir reduction for this transcript and the reduced-round hash assumption; Merkle/chain binding errors enter once.

---

**WHIR parameters.** k lists folds per round, t query counts, b PoW bits; ℓ_lookup and ℓ_batch are lookup/batching PoW counts.

```text
Ordinary 2²⁴-row instruction chunk (4 main layers, 366 cubic messages):
  k = (1,5,5,5,4,3); t = (89,23,10,7,5,5); b = (26,24,25,19,21,21)
  final coefficients = 2
Ordinary unified, 2²³ rows (4 main layers, 339 cubic messages):
  k = (1,5,5,5,4); t = (89,23,10,7,5); b = (26,24,25,19,21)
  final coefficients = 8; (ℓ_lookup,ℓ_batch) = (9,8)
Merged unified feeder, 2²³ rows (same GKR/fold counts):
  t = (21,17,9,5,4); b = (29,26,25,26,21)
  final coefficients = 8; (ℓ_lookup,ℓ_batch) = (9,11)
```

For unrolled memory, assuming Algorithm 2's charges bound the compiled event counts, let n_f,n_d,n_IT be the proof counts and ℓ_f the instruction trace logarithms:

```text
N ≤ 4Σ_f n_f2^ℓ_f + Σ_d n_dA_d + 8n_IT2²⁴ + 33
  ≤ (2⁴⁰−1) + 2³⁰ + 33
ε_mem ≤ Nμ < 2^(−81.65)             // before computational PoW accounting
```

The 33 boundary events are the ordinary registers and PC. A unified bound must include its authenticated IT products.

**References:** [GKR](https://people.cs.georgetown.edu/jthaler/GKRNote.pdf), [LogUp](https://eprint.iacr.org/2022/1530), [GKR lookup compression](https://eprint.iacr.org/2023/1284), [WHIR](https://eprint.iacr.org/2024/1586), [Two Shuffles Make a RAM](https://eprint.iacr.org/2023/1115).

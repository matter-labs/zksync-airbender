---
class: protocol-appendix-light
---

# Appendix — Protocol algorithms and soundness

Parameter reference: BabyBear `Sec100`, `av_gkr_compiler` at [`c1a6622`](https://github.com/matter-labs/zksync-airbender/commit/c1a662222cafcd96db4383dce737edb79fa62b09).

```text
FullStatement
  ├─ VerifyChunks → Chunk → GKR layers → OutputChecks → WHIR
  ├─ CloseMemory → equal event multisets → machine execution
  └─ FinishChain → (application result, program-history digest)
Recursive step: prove the execution of FullStatement; repeat.
```

> **Fiat–Shamir challenges**
>
> **Parameters:** seven-round BLAKE2s with messages absorbed as raw 32-bit words. $E$ is BabyBear's quartic extension, with base modulus $p=2^{31}-2^{27}+1$.
>
> **Proof of work (PoW).** When challenge drawing requires $b$ bits of proof of work, the prover supplies a 64-bit nonce, which is absorbed into the transcript immediately before drawing. The first drawn 32-bit word is reserved for PoW: the verifier accepts only if it has $b$ leading zero bits. Field challenges are sampled from subsequent drawn words. For $b=0$, the nonce is still absorbed and the first drawn word is still reserved, but every nonce passes.
>
> **Transcript flow across the proof.** `FullStatement` first absorbs the final state (register values, PC and timestamps) and all chunks' memory commitments (Merkle tree caps), with circuit-family identifiers and RAM initialization/teardown window identifiers. These identify the circuit types and RAM ranges associated with the commitments. Before absorbing a Merkle-cap sequence, it zero-pads to the next block boundary; successive absorb calls otherwise concatenate without padding. This precommitment binds the selected memory events before the shared challenges $\mathbf{r}_{\mathrm{mem}}$ are drawn (Algorithms 1–2).
>
> Each chunk starts a fresh transcript by absorbing its window identifiers, $\mathbf{r}_{\mathrm{mem}}$, and commitments to its setup, memory and remaining witness, omitting absent witness groups (Algorithm 3). Chunk transcripts proceed in parallel through GKR and WHIR; in the end, chunks' verified memory products are combined without further challenges.
>
> **Modular reduction sampling.** Each base-field challenge is a drawn 32-bit word reduced modulo $p$. Each extension-field challenge combines four such samples as coefficients in a fixed basis of $E$. Assuming independent uniform transcript words, each reduced coefficient has at most three preimages. For any fixed $a \in E$:
>
> $$
> \Pr[\text{challenge} = a] \le \mu = \left(\frac{3}{2^{32}}\right)^4 = \frac{81}{2^{128}} \approx 2^{-121.66}
> $$
>
> This accounts for modulo bias, so a fixed nonzero polynomial of total degree $d$ vanishes with probability $\le d\mu$ under independent challenge sampling.
>
> **Soundness.** In an idealized model with fresh, independent uniform draw words, for any algebraic check using challenges from a PoW-protected absorb–draw round and any transcript prefix and candidate nonce chosen before seeing those words:
>
> $$
> \Pr[\text{PoW check passes}\;\land\;\text{a false algebraic claim is accepted}] \le 2^{-b}\varepsilon
> $$
>
> where $\varepsilon$ bounds the algebraic soundness error of the ensuing protocol step, conditioned on the preceding transcript and no earlier soundness failure. The protocol analyses below determine $\varepsilon$, including sampling bias through $\mu$ and any permitted adaptive continuation. Composition accounts for all such rounds, adversarial attempts, and earlier soundness failures. A Fiat–Shamir soundness reduction in the random-oracle model remains to be established.

---

> **Algorithm 1 — FullStatement**
>
> **Variable Configuration**
>
> Prover and verifier use common values for the following parameters, fixed throughout the protocol:
>
> - $\mathrm{profile}\in\{\mathrm{unrolled},\mathrm{unified}\}$. Unrolled uses separate instruction-family circuits; unified uses one combined instruction-family circuit (delegation circuits stay separate).
> - $\mathrm{mode}\in\{\mathrm{base},\mathrm{continuation}\}$. Base starts a new program-history chain and is meant for proving application execution; continuation validates and continues an incoming chain and is meant for proving recursive verifier execution.
> - $\mathrm{commitment\text{-}config}\in\{\mathrm{ordinary},\;\mathrm{merged\text{-}feeder}\ \text{if}\ \mathrm{profile}=\mathrm{unified}\land\mathrm{mode}=\mathrm{continuation}\}$: ordinary uses separate Merkle trees for memory and remaining-witness columns; merged-feeder commits both column groups under one shared Merkle tree. The two options further impose restrictions on the WHIR (Algorithm 7) trace dimensions, LDE ratios, query counts, and PoW grinding difficulties selected for instruction circuits by Algorithm 12. Delegation circuits select their ordinary circuit-specific parameters independently of this setting.
>
> **Protocol**
>
> 1. Prover sends `ProgramSetupCaps`, Merkle caps of the program-dependent instruction setup columns (one per configured unrolled instruction family, in family-id order, or a single unified circuit cap), followed by the final RISC-V register values $x_j$ and timestamp limbs, then PC and timestamp limbs. The claimed final state contains 99 raw 32-bit words:
>
>    $$
>    \mathrm{fin}=\bigl((x_j,\mathrm{ts}_{j,\mathrm{lo}},\mathrm{ts}_{j,\mathrm{hi}})_{j=0}^{31},(\mathrm{pc},\mathrm{ts}_{\mathrm{pc},\mathrm{lo}},\mathrm{ts}_{\mathrm{pc},\mathrm{hi}})\bigr).
>    $$
>
>    The register timestamps record each register's last access; the PC timestamp records the final machine time. Verifier requires $x_0=0$.
> 2. Using the layouts selected by Algorithm 12, prover constructs and commits all participating memory columns from the execution witness; for merged-feeder instruction chunks, the same cap also commits the remaining witness columns. The memory caps and family/window identifiers form $\mathcal M$ (Algorithm 2). Prover initializes the transcript with the 32 final register triples, then PC/timestamp; zero-pads to fill the current input block (13 words), then absorbs $\mathcal M$. It finds a 19-bit PoW nonce, derives and sends:
>
>    $$
>    \mathbf{r}_{\mathrm{mem}}=(r_{\mathrm{mem},0},\ldots,r_{\mathrm{mem},5},\eta)\in E^7
>    $$
>
> 3. Prover sends the chunk counts and associated proofs in Algorithm 2 order. Verifier runs `VerifyChunks` with the selected settings, `ProgramSetupCaps`, $\mathbf r_{\mathrm{mem}}$ and the counted proofs, obtaining $\mathrm{RS},\mathrm{WS}\in E$ (read/write product accumulators). It reconstructs $\mathcal M$ from the verified chunks' memory caps and identifiers, and the transcript from $\mathrm{fin}$ and $\mathcal M$, as in step 2.
> 4. Prover sends the 64-bit memory-PoW nonce. Verifier checks the 19-bit PoW and derives the challenges from the reconstructed transcript; require equality with the supplied $\mathbf r_{\mathrm{mem}}$.
> 5. Run $\operatorname{CloseMemory}(\mathrm{fin},\mathbf{r}_{\mathrm{mem}},\mathrm{RS},\mathrm{WS})$. In continuation mode, prover then sends the 16-word hash-chain preimage.
> 6. Return `FinishChain` applied to `ProgramSetupCaps`, $\mathrm{fin}$, mode and any supplied preimage: the application result $x_{10},\ldots,x_{17}$ and program-history digest $h_0,\ldots,h_7$, each eight 32-bit words (Algorithm 10). The digest records setup/ending-PC identities with consecutive repetitions collapsed. The terminal caller checks the expected program identity, successful ending PC and history (Algorithm 11). Reject if any check fails.
>
> **Soundness — composition (adapted).** Chunk relations and CloseMemory establish execution under the reconstruction lemmas in Algorithm 9. The memory prefix must fix every selected memory factor before $\mathbf{r}_{\mathrm{mem}}$. Proof counts, `ProgramSetupCaps` and separate witness caps are not absorbed into that prefix; setup/witness caps enter chunk transcripts. Required binding lemma: the encoding of $\mathcal M$ and committed columns fix the participating event collection despite these omissions.

---

> **Algorithm 2 — VerifyChunks**
>
> **Configuration:** profile, mode and commitment-config from Algorithm 1 fix the circuit families, their order, delegation setups and proof parameters.
>
> **Input:** `ProgramSetupCaps`, shared $\mathbf{r}_{\mathrm{mem}}$, participant counts and chunk proofs carrying the memory caps and window identifiers. **Output:** accumulated read/write products $\mathrm{RS},\mathrm{WS}\in E$.
>
> **Memory commitments and family/window identifiers $\mathcal M$**, reconstructed from the counted proofs and configured family identifiers, in transcript order. After each identifier group below, zero-pad to fill the current transcript input block:
>
> - **Unrolled:** for each nonempty instruction family, its family-identifier block followed by its memory caps in proof order; then the IT (RAM initialization/teardown) family-identifier block followed by each IT cap and a block of its eight window identifiers.
> - **Unified:** for each chunk, one block containing the unified-family identifier and its two window identifiers, then its memory cap.
> - **Both:** append each nonempty delegation-type identifier block followed by its memory caps in proof order. Counts are not separately absorbed.
>
> **Verification**
>
> 1. Select the instruction families from profile/mode and the fixed delegation families listed below. For merged-feeder, require unified continuation mode. Initialize $\mathrm{RS}\leftarrow1$, $\mathrm{WS}\leftarrow1$.
> 2. For each family in the configured order, prover sends a chunk count followed by that many proofs; verifier reads and processes them in that order. For unified, prover sends the total chunk count and the number of trailing IT-carrying chunks before the proofs. For each chunk:
>    1. Verify its Chunk with the memory commitment and window identifiers from $\mathcal M$ and the shared $\mathbf{r}_{\mathrm{mem}}$.
>    2. Require each instruction setup cap to match its family in `ProgramSetupCaps`; every unified chunk must match `ProgramSetupCaps[0]`. Delegation setup caps must match the verifier's fixed cap for that type; standalone IT has no setup cap.
>    3. Multiply the verified ordinary read/write products into $\mathrm{RS},\mathrm{WS}$.
>    4. For a trailing IT-carrying unified chunk, require its additional IT pair and multiply it into $\mathrm{RS},\mathrm{WS}$. Exclude this pair for leading unified chunks.
> 3. Enforce the IT partition and disjointness rules:
>    - **Unrolled:** $1\le n_{\mathrm{IT}}\le8$. Each IT proof contributes eight window identifiers; their concatenation is strictly increasing in $[0,64)$.
>    - **Unified:** $n>0$ and $1\le n_{\mathrm{IT}}\le n$. The first $n-n_{\mathrm{IT}}$ chunks have both identifiers zero. The last $n_{\mathrm{IT}}$ chunks carry IT products; their two identifiers per chunk are strictly increasing in $[0,64)$.
> 4. Enforce the integer capacity bounds:
>
>    $$
>    \begin{aligned}
>    \mathrm{cycles}&<2^{36} \\
>    4\,\mathrm{cycles}+\sum_d n_dA_d&<2^{40}
>    \end{aligned}
>    $$
>
>    Here $n_f,n_d$ count instruction/delegation chunks, $\ell_f$ is the instruction trace logarithm, and $A_d$ is the delegation event-capacity charge. Set $\mathrm{cycles}=\sum_f n_f2^{\ell_f}$ for unrolled instructions, or $n2^{24}$ for unified chunks.
> 5. Return $\mathrm{RS},\mathrm{WS}$.
>
> **Soundness — participant/window binding (new).** Setup checks fix program/precompile tables. Matching each chunk to $\mathcal M$ transfers the prechallenge commitment and window binding to its products. Strictly increasing, circuit-bound IT windows prevent repeated initialization/teardown. Requires the capacity charges to bound the circuit's event counts.

---

> **Algorithm 3 — Chunk**
>
> **Public data:** shared $\mathbf{r}_{\mathrm{mem}}$, caps and window identifiers $b$. **Prover data:** column tables $M,W,S$ and intermediate gate values; lookup multiplicities belong to $W$. **Relation:** $C$'s gates/zero constraints and selected lookup memberships hold; exported products equal the selected memory-event products. **Output:** verified products, `MemoryCaps`, `SetupCaps`, $b$.
>
> **Notation:** $C$ is the compiled arithmetic circuit selected by the verifier, on $2^n$ rows. Its wiring, zero constraints, column order, lookup tables and auxiliary relations are fixed public parameters; Algorithm 12 selects the proof parameters. $M,W,S$ are BabyBear-valued memory, remaining witness and setup columns, committed by `MemoryCaps`, `WitnessCaps`, `SetupCaps`; virtual setup tables are evaluated directly by the verifier; $\operatorname{MLE}(A)$ is table $A$'s multilinear extension.
>
> 1. Select the chunk parameters from its fixed circuit description, role and commitment-config (Algorithm 12). Prover sends $b$ and cap hashes in setup/memory/witness order. The selected circuit and commitment-config fix the cap counts, cap sizes and column grouping; these are not read from the proof:
>    - **Ordinary chunks:** separate `MemoryCaps` and `WitnessCaps` for nonempty memory and remaining-witness groups, and `SetupCaps` for committed setup columns.
>    - **Merged-feeder instruction chunks:** `SetupCaps` and `MemoryCaps`, where `MemoryCaps` commits to $M\mathbin{\|}W$ in that column order. No separate witness cap is read.
>    - **Standalone IT:** `MemoryCaps` only.
>
>    The witness $W$, including multiplicities, is fixed at this point; in merged-feeder instruction chunks it was already committed before $\mathbf r_{\mathrm{mem}}$. Verifier starts a fresh transcript $T$ from the ordered prefix below, omitting cap groups absent from the configured layout:
>
>    $$
>    b\mathbin{\|}\mathbf{r}_{\mathrm{mem}}\mathbin{\|}\mathtt{SetupCaps}\mathbin{\|}\mathtt{MemoryCaps}\mathbin{\|}\mathtt{WitnessCaps}
>    $$
>
>    Each chunk initializes independently from this prefix; no memory-transcript seed is inherited.
> 2. Prover sends the lookup-PoW nonce. Verifier checks the lookup-PoW threshold from Algorithm 12 and draws $(\alpha,\beta)\in E^2$.
> 3. Prover evaluates $C$ forward, accumulates outputs to sixteen entries and sends tables $A_0,\ldots,A_{s-1}$. Verifier absorbs the tables, draws $(u_0,\ldots,u_3,\lambda)$ and sets $a_j\leftarrow\operatorname{MLE}(A_j)(u)$.
> 4. For $k=4,\ldots,n-1$, run $\operatorname{GKRLayer}(\mathrm{compression},k)$. Then run $\operatorname{GKRLayer}(\mathrm{main},n)$ for each main layer, from outputs towards inputs, obtaining base-column claims $f_j(\zeta)=a_j$.
> 5. Prover sends the batching/proximity-PoW nonce. Verifier checks the batching-PoW threshold from Algorithm 12 and draws $\gamma\in E$.
> 6. Obtain the product pairs from $\operatorname{OutputChecks}(A_0,\ldots,A_{s-1})$.
> 7. Run $\operatorname{WHIR}(\mathrm{base\ caps},\zeta,a,\gamma,T)$ with the selected oracle layout, Reed–Solomon domains, fold/query schedule and PoW thresholds (Algorithm 7 and parameters below). Return the products, `MemoryCaps`, `SetupCaps` and $b$.
>
> WHIR continues the GKR transcript. These BabyBear instances are unpacked. Packed instances draw fresh pack coordinates after the main layers, merge claims within each commitment set by multilinear weights, and append the coordinates to $\zeta$ before the batching PoW.
>
> **Soundness — local reduction (adapted).** GKR reduces output-table claims to base openings established by WHIR. Queries, selectors and multiplicities must be fixed before $\alpha,\beta$. Product/lookup compression is included in $\varepsilon_{\mathrm{GKR}}$.

---

> **Algorithm 4 — EQSumcheck**
>
> **Input:** incoming point $u \in E^k$ and batched claim $v$ for gate polynomial $G$, of individual degree $\le 2$. **Output:** point $r$, scalar $v$, last EQ factor $e$.
>
> **Notation:** $\operatorname{eq}(u,x) = \prod_j((1-u_j)(1-x_j)+u_jx_j)$, the Boolean-cube interpolation kernel.
>
> 1. Initialize $e \leftarrow 1$.
> 2. For each $j = 0,\ldots,k-1$:
>    1. Prover sends the coefficients of $g_j(X)$, with $\deg g_j \le 3$.
>    2. Verifier requires $e\,(g_j(0)+g_j(1)) = v$.
>    3. Absorb the coefficients, then derive $r_j\in E$ from the chunk transcript.
>    4. Update:
>
>       $$
>       \begin{aligned}
>       v &\leftarrow g_j(r_j) \\
>       e &\leftarrow (1-r_j)(1-u_j)+r_j u_j
>       \end{aligned}
>       $$
>
> 3. Return $(r,v,e)$.
>
> Honest $g_j(X) = \operatorname{eq}(u_j,X)\sum_{x'\in\{0,1\}^{k-j-1}}\operatorname{eq}(u_{>j},x')G(r_{<j},X,x')$. The caller closes with $v=e\,G(r)$.
>
> **Soundness — Sumcheck (standard), EQ factoring (adapted).** Conditional on $e\ne 0$, each false cubic identity survives with probability $\le 3\mu$. The new factor is $1-u_j+(2u_j-1)r_j$: it is $1/2$ when $u_j=1/2$, otherwise it has one root, costing $\le\mu$. Thus $k$ rounds cost $\le(3k+Z)\mu$ with $Z\le k$ charged EQ-zero events, provided the final gate evaluation is established downstream.

---

> **Algorithm 5 — GKRLayer**
>
> **Input:** output claims $(u,a)$, batching challenge $\lambda$ and fixed circuit layer $C$.
>
> **Notation:** `Batch` uses $C$'s power order in $\lambda$ and includes claim $0$ for every zero constraint. `Gate` is the same batched gate expression, evaluated by the verifier.
>
> 1. Set $v\leftarrow\operatorname{Batch}(a\text{ and zero claims};\lambda)$; obtain $(r,v,e)\leftarrow\operatorname{EQSumcheck}(u,v)$.
> 2. **Compression layer:**
>    1. Prover sends $h_j(0,r),h_j(1,r)$ for every required input.
>    2. Verifier requires $v=e\,\operatorname{Gate}(\text{endpoint values};\lambda)$; absorb all endpoints and draw $(t,\lambda')$.
>    3. For each $j$, set:
>
>       $$
>       a'_j\leftarrow(1-t)h_j(0,r)+t\,h_j(1,r)
>       $$
>
>    4. Return $((t,r),a',\lambda')$.
> 3. **Otherwise, main layer:**
>    1. Prover sends the required input evaluations at $r$.
>    2. Verifier requires $v=e\,\operatorname{Gate}(\text{input values};\lambda)$.
>    3. Prover sends the additional evaluations required by $C$'s auxiliary polynomial relations. Verifier absorbs these together with the input evaluations and draws $\lambda'$.
>    4. Check $C$'s auxiliary relations and publicly evaluable setup polynomials. Return the preceding-layer claims at $r$ in $C$'s fixed input-polynomial order, and $\lambda'$.
>
> Compression gates: product $h_0h_1$; rational sum $(n_0d_1+n_1d_0,d_0d_1)$. The verifier evaluates public setup polynomials directly; committed setup polynomials become WHIR opening claims.
>
> **Soundness — GKR (adapted).** An initial false sixteen-entry table test costs $\le(4+b-1)\mu$ for $b$ tables; each further power batch of $b$ fixed claims costs $\le(b-1)\mu$. Endpoint interpolation adds a degree-one test for fixed endpoint discrepancies. For $L$ main layers, $R=\sum_{k=4}^{n-1}k+Ln$ cubic messages. Then $\varepsilon_{\mathrm{GKR}}\le\min(1,\mu(4+B+3R+Z+S))$, $Z\le R$, where $B$ counts batching degrees and $S$ the remaining point/line tests. Requires the layer, auxiliary-relation and public-polynomial induction and instantiated $B,S$ counts.

---

> **Algorithm 6 — OutputChecks: memory products and LogUp**
>
> **Input:** original sixteen-entry tables.
>
> **Notation:** $Q$ is the query multiset and $T$ the lookup table; $m_t$ is table tuple $t$'s committed multiplicity. Tuples have width $w$, including any table identifier. With lookup challenges $\alpha,\beta$, define $\ell(t)=\beta+\sum_{j=0}^{w-1}\alpha^j t_j$.
>
> 1. For each ordinary or embedded-IT product pair $(A_R,A_W)$, compute:
>
>    $$
>    \begin{aligned}
>    R &\leftarrow \prod_{j=0}^{15}A_R[j] \\
>    W &\leftarrow \prod_{j=0}^{15}A_W[j]
>    \end{aligned}
>    $$
>
> 2. For each present lookup pair $(A_N,A_D)$:
>    1. Initialize $N\leftarrow 0$, $D\leftarrow 1$.
>    2. For $j=0,\ldots,15$, update simultaneously:
>
>       $$
>       (N,D)\leftarrow\bigl(N\,A_D[j]+A_N[j]D,\;D\,A_D[j]\bigr)
>       $$
>
>    3. Require $N=0$ and $D\ne 0$.
> 3. Return the product pairs.
>
> The leaf relation is $\sum_{q\in Q}1/\ell(q)=\sum_{t\in T}m_t/\ell(t)$. Its rational compression tree is proved by GKR with base openings in WHIR. The 16-bit and timestamp virtual tables have $2^{16}$ and $2^{19}$ entries. IT has zero categories; BLAKE and Keccak have two; the other listed circuits have three. The fixed arithmetic circuit determines selectors and padding queries.
>
> **Soundness — LogUp (standard), encodings/counts (adapted).** For nonzero denominators and fixed tuples/multiplicities, a false rational identity gives a nonzero polynomial after clearing denominators. Thus $\varepsilon_{\mathrm{lookup}}\le\mu\sum_a D_a$, with $D_a\le T_a\max(1,w_a)$ for $T_a$ fraction occurrences in category $a$. Membership requires invalid-tuple query counts to be nonzero modulo $p$; fewer than $p$ query occurrences per category suffices. Requires per-circuit occurrence bounds; field-valued multiplicities do not themselves bound integer counts. The union bound applies with shared $\alpha,\beta$.

---

> **Algorithm 7 — WHIR**
>
> **Input:** base cap hashes; claims $f_j(\zeta)=a_j$; $\gamma$; the Chunk transcript $T$ continued after GKR. **Fixed parameters:** round folds $k_r$, query counts $t_r$, PoW thresholds $b_r$, Reed–Solomon domains, cap sizes, column grouping, leaf widths, authentication-path depths and final coefficient count, selected by the circuit and commitment-config. **Witness:** base and folded polynomials and authenticated leaves. **Relation:** the committed base polynomials have the claimed evaluations and required encoding/degree bounds.
>
> **Notation:** $f_j$ are column MLEs and $\zeta$ their opening point. For monomial coefficients $c_t$, $F_f(X)=\sum_t c_tX^t$ and $\operatorname{powers}(s)=(s,s^2,s^4,\ldots)$, so $F_f(s)=f(\operatorname{powers}(s))$; low-index bits select the first folded variables. $\operatorname{eq}$ is the interpolation kernel from EQSumcheck; $w$ is the running weight function, $m$ the remaining dimension and $D_r$ the current Reed–Solomon evaluation domain.
>
> 1. Use the domains, leaf widths, path depths and final coefficient count from Algorithm 12. Prover batches $f$; verifier initializes $v,w$:
>
>    $$
>    \begin{aligned}
>    f &\leftarrow \sum_j\gamma^j f_j \\
>    v &\leftarrow \sum_j\gamma^j a_j \\
>    w(x) &\leftarrow \operatorname{eq}(\zeta,x)
>    \end{aligned}
>    $$
>
>    Maintain $v=\sum_{x\in\{0,1\}^m}f(x)w(x)$. The current oracle is the committed base columns in memory/witness/setup order.
> 2. For each nonfinal round $r$:
>    1. Run $k_r$ QuadraticSteps, obtaining fold challenges $a$. These steps have already restricted $f,w$.
>    2. Prover sets $f_{\mathrm{next}}\leftarrow f$ and sends a cap committing to the proposed $f_{\mathrm{next}}$.
>    3. Verifier absorbs that cap and draws $\xi$.
>    4. Prover sends $u$, claimed as $F_{\mathrm{next}}(\xi)$. Verifier absorbs $u$, checks the $b_r$-bit PoW, draws query indices $I_0,\ldots,I_{t_r-1}$ uniformly from $[0,|D_r|/2^{k_r})$ with replacement (one index per fold group), then derives $\delta$ from fresh hash output beyond the query-index randomness.
>    5. For each query $j=0,\ldots,t_r-1$:
>       1. Prover sends current-oracle leaves and Merkle paths.
>       2. Verifier reads the configured number of values per leaf, authenticates each leaf against its cap at the configured tree position and computes $q_j\leftarrow\operatorname{Fold}(\mathrm{leaves},a)$.
>       3. Set $s_j\leftarrow(\omega^{I_j})^{2^{k_r}}$, where $\omega$ generates the current oracle's domain.
>    6. Verifier updates:
>
>       $$
>       \begin{aligned}
>       w &\leftarrow w+\delta\,\operatorname{eq}(\operatorname{powers}(\xi),\cdot) \\
>         &\quad +\sum_{j=0}^{t_r-1}\delta^{j+2}\operatorname{eq}(\operatorname{powers}(s_j),\cdot) \\
>       v &\leftarrow v+\delta u+\sum_{j=0}^{t_r-1}\delta^{j+2}q_j
>       \end{aligned}
>       $$
>
>    7. Continue with $f\leftarrow f_{\mathrm{next}}$ and its commitment as the next round's oracle.
> 3. Final round:
>    1. Run the final $k_r$ QuadraticSteps.
>    2. Prover sends exactly $2^{n-\sum_r k_r}$ monomial coefficients $c$ of the remaining polynomial.
>    3. Verifier absorbs $c$, checks the final PoW and draws the final query indices as in step 2.4.
>    4. Authenticate/fold the current-oracle leaves, defining $s_j$ as in step 2. For each query require $q_j=\sum_l c_l s_j^l$.
>    5. Reconstruct $f_{\mathrm{final}}$ from $c$ and require:
>
>       $$
>       v=\sum_{x\in\{0,1\}^m}f_{\mathrm{final}}(x)w(x)
>       $$
>
> 4. Accept the base-opening claims.
>
> The same fold challenges restrict $f,w$ and the authenticated leaves. The first round opens evaluation leaves from every nonempty base oracle: separate memory/witness/setup trees for ordinary instruction chunks, or merged memory/witness and separate setup trees for merged-feeder instruction chunks. Both layouts batch the columns in the same memory/witness/setup order with the claims' $\gamma$ powers; later rounds open coefficient leaves from the preceding fold commitment (Algorithm 8). Merkle paths are checked but not absorbed. Query evaluations constrain $f_{\mathrm{next}}$. For $m$ remaining variables, $\deg(F_f)<2^m$; the schedule fixes Reed–Solomon domains and expansion factors.
>
> **Soundness — WHIR (adapted).** Assume binding caps and a proximity/list-decoding bound for both leaf encodings, accumulator and capacity-based schedule. For $c$ columns, batching costs $\le(c-1)\mu$; each quadratic step $\le 2\mu$; each $\delta$ combination $\le(t_r+1)\mu$; a fixed false degree-$d$ OOD equality $\le d\mu$. For a fixed candidate and fold challenges, let $a$ be the fraction of fold groups where the candidate agrees with the authenticated fold. It survives $t$ independent queries with probability $\le a^t$. Requires a derivation of fold-group agreement and candidate-list bounds from Reed–Solomon proximity for every round. Using disjoint error terms, $\varepsilon_{\mathrm{PCS}}\le\varepsilon_{\mathrm{batch}}+\varepsilon_{\mathrm{proximity/list}}+\varepsilon_{\mathrm{OOD}}+\varepsilon_{\mathrm{query}}+\varepsilon_{\mathrm{combine}}+\varepsilon_{\mathrm{quadratic}}+\varepsilon_{\mathrm{binding}}$.

---

> **Algorithm 8 — QuadraticStep and Fold**
>
> **Input:** running claim $v$, current $f,w$; authenticated leaf data with the round's encoding from Algorithm 7.
>
> **Notation:** $a=(a_0,\ldots,a_{k-1})$ are fold challenges; $c_b$ are authenticated local monomial coefficients. $x$ is a nonzero coset point; $F_f$ is the univariate encoding of $f$. The $\kappa$ values are weights of restricted EQ terms.
>
> **QuadraticStep**
>
> 1. Prover sends three coefficients of $h(X)$, with $\deg h\le 2$, claiming $h(X)=\sum_x f(X,x)w(X,x)$.
> 2. Verifier requires $h(0)+h(1)=v$; absorb its coefficients and draw $a$ from the transcript.
> 3. Prover restricts $f$; verifier updates $v,w$:
>
>    $$
>    \begin{aligned}
>    f &\leftarrow f(a,\cdot) \\
>    v &\leftarrow h(a) \\
>    w &\leftarrow w(a,\cdot)
>    \end{aligned}
>    $$
>
> 4. Return $a$.
>
> **Fold — coefficient leaves**
>
> 1. Return:
>
>    $$
>    \sum_{b\in\{0,1\}^k}c_b\prod_{j=0}^{k-1}a_j^{b_j}
>    $$
>
> **Fold — evaluation leaves**
>
> 1. For each fold challenge $a_j$:
>    1. Pair $A=F_f(x)$, $B=F_f(-x)$ in the configured coset order.
>    2. Replace each pair by:
>
>       $$
>       \frac{A+B+a_j(A-B)/x}{2}
>       $$
>
>    3. Square the coset points between fold steps.
> 2. Return the remaining value.
>
> **Soundness — Sumcheck (standard), encoding map (adapted).** Requires the coset/bit-reversal map to match the leaf encoding. Coefficient leaves contain local monomial tensors. Restricting the EQ terms gives the final cube sum $\kappa_0 f_{\mathrm{final}}(\zeta_{\mathrm{remaining}})+\sum_j\kappa_j F_{\mathrm{final}}(s_j)$, where each OOD/query scalar is squared at every subsequent coordinate restriction.

---

> **Algorithm 9 — CloseMemory**
>
> **Input:** final state $\mathrm{fin}$, $\mathbf{r}_{\mathrm{mem}}$, authenticated products $\mathrm{RS},\mathrm{WS}$.
>
> **Notation:** $R,W$ are read/write event multisets; $\mathbf{r}_{\mathrm{mem}}=(r_{\mathrm{mem},0},\ldots,r_{\mathrm{mem},5},\eta)$. In event $t=(a,t_0,\ldots,t_5)$, the limbs are address lo/hi, timestamp lo/hi, value lo/hi; tags are 0 = register, 1 = RAM, 2 = PC. Define $L_{\mathbf{r}_{\mathrm{mem}}}(t)=a+\eta+\sum_{j=0}^5r_{\mathrm{mem},j} t_j$ with six independent coefficients.
>
> 1. Form `Initial` from the ordinary-register writes $x_0,\ldots,x_{31}$ of value 0 at time 0, and the PC write with value 0 at time 4. Form `Final` from the 32 register reads and PC read specified by $\mathrm{fin}$.
> 2. Include the boundary factors:
>
>    $$
>    \begin{aligned}
>    \mathrm{WS} &\leftarrow \mathrm{WS}\prod_{t\in\mathrm{Initial}}L_{\mathbf{r}_{\mathrm{mem}}}(t) \\
>    \mathrm{RS} &\leftarrow \mathrm{RS}\prod_{t\in\mathrm{Final}}L_{\mathbf{r}_{\mathrm{mem}}}(t)
>    \end{aligned}
>    $$
>
> 3. Require $\mathrm{RS}=\mathrm{WS}$. RAM boundaries already enter through IT products.
>
> Chunk transcripts end independently. This product equality uses the shared $\mathbf{r}_{\mathrm{mem}}$ and requires no further challenges or transcript merge.
>
> **Soundness — fingerprint (standard), event encoding (adapted).** Assume $R,W$ are fixed before $\mathbf{r}_{\mathrm{mem}}$ and their encoding is injective. Unequal multisets give a nonzero difference of products: each affine factor has $\eta$-coefficient 1, so unique factorization distinguishes multisets. Hence $\varepsilon_{\mathrm{mem}}\le N\mu$, $N=\max(|R|,|W|)$, once per statement. Boundary values use 16-bit limbs; supplied timestamp limbs are reduced modulo $p$ without a 19-bit check here. Requires injectivity on accepted boundary data.
>
> **Soundness — execution reconstruction (adapted/new).** Required reconstruction lemma: equal events, local relations and authenticated setups imply an execution from $(\mathrm{pc},\mathrm{time})=(0,4)$ and zero ordinary registers/RAM to $\mathrm{fin}$. Its premises include initialization/IT coverage, strict timestamp growth, PC connectivity, decoder membership, delegation matching, inactive-row neutrality and range propagation.

---

> **Algorithm 10 — FinishChain**
>
> **Input:** program setups `ProgramSetupCaps`, final state $\mathrm{fin}$, base/continuation mode and, for continuation, the preimage $(h_{\mathrm{prev}},e_{\mathrm{prev}})$ (eight 32-bit words each). **Output:** $(y,h)$.
>
> **Notation:** $x_j$ and $\mathrm{pc}$ come from $\mathrm{fin}$; `Hash` uses the transcript's seven-round BLAKE2s and word encoding.
>
> 1. Set $y\leftarrow(x_{10},\ldots,x_{17})$ and:
>
>    $$
>    e\leftarrow\operatorname{Hash}\bigl((\mathrm{pc},0^{15})\mathbin{\|}\mathtt{ProgramSetupCaps}\bigr)
>    $$
>
>    After PC, zero-pad to fill the current transcript input block (15 words), then absorb the ordered setup caps. Timestamps are excluded.
> 2. **Base mode:** require $(x_{18},\ldots,x_{25})=0^8$; set $h\leftarrow\operatorname{Hash}(0^8\mathbin{\|}e)$.
> 3. **Otherwise, continuation mode:**
>    1. Set $h_{\mathrm{in}}\leftarrow(x_{18},\ldots,x_{25})$.
>    2. Prover supplies the hash-chain preimage $(h_{\mathrm{prev}},e_{\mathrm{prev}})$; require $\operatorname{Hash}(h_{\mathrm{prev}}\mathbin{\|}e_{\mathrm{prev}})=h_{\mathrm{in}}$.
>    3. **If $e_{\mathrm{prev}}=e$:** set $h\leftarrow h_{\mathrm{in}}$.
>    4. **Otherwise:** set $h\leftarrow\operatorname{Hash}(h_{\mathrm{in}}\mathbin{\|}e)$.
> 4. Return $(y,h)$.
>
> **Soundness — program-history binding (new).** Under hash binding and authenticated verifier executions, $h$ commits to the sequence of setup/ending-PC identities with consecutive repetitions collapsed. Terminal acceptance checks the expected setup identity, successful ending PC and expected chain; depth/work requires an external bound.

---

> **Algorithm 11 — Recursion and terminal acceptance**
>
> **Public claim:** application identity, expected collapsed verifier history and result $y$. **Witness:** child proof bundle and its verifier-execution trace. **Recursive relation:** the selected verifier program runs `FullStatement` on the child and reaches its successful return with $(y,h)$ in $x_{10},\ldots,x_{25}$.
>
> 1. Prove the application execution:
>    - **If unrolled:** use unrolled circuits; verify with the base unrolled verifier.
>    - **If unified:** use unified circuits; verify with the base unified verifier.
> 2. Optionally repeat, proving the selected verifier's execution:
>    - **If unrolled:** use unrolled circuits; verify with the unrolled continuation verifier.
>    - **If unified:** use unified circuits; verify with the unified continuation verifier.
> 3. **Bridge (if switching from unrolled to unified):** prove the selected unrolled base/continuation verifier's execution with unified circuits; verify with the unified continuation verifier, then repeat step 2 as needed using unified circuits.
> 4. **Terminal acceptance:**
>    1. Verify the last proof with `FullStatement`, obtaining $(y,h)$.
>    2. Require its `ProgramSetupCaps` and final PC to match the expected setup caps and successful ending PC, and require $h=h_{\mathrm{expected}}$.
>    3. Accept and expose $y$ only if all verification and expectation checks pass; otherwise reject.
>
> Expected identities and $h_{\mathrm{expected}}$ are determined by the application starting values and selected recursive configuration. The L1 route uses a merged-commitment feeder, then a packed Proth120 proof with a Keccak transcript, and must enforce the same expectation checks. Its serialization, public-claim mapping and contract linkage require a separate protocol.
>
> **Soundness — recursive composition (adapted).** Outer execution soundness and authenticated verifier identity/success imply child acceptance. Induction requires these conditions at every handoff and an external depth/work bound; the composed error sums over the proved invocations.

---

**Circuit and memory parameters.** Merkle caps contain sixteen 256-bit hashes. The profile fixes the following family order, row counts and capacity charges.

- **Unrolled instructions:** add/sub/LUI/AUIPC/MOP; jump/branch/compare; shift/binary; unsigned multiply/divide; word memory; subword memory. Continuation omits multiply/divide and subword memory. Trace logarithms are 24 except multiply/divide, which uses 23.
- **Delegations:** BLAKE2s, bigint, Keccak special5, theta/rho, column parity and chi5, with trace logarithms $(20,22,22,22,22,22)$ and charges $A_d=(44\cdot2^{20},20\cdot2^{22},15\cdot2^{22},17\cdot2^{22},15\cdot2^{22},13\cdot2^{22})$ in that order.
- **IT windows:** standalone IT has $2^{24}$ rows and eight windows of $2^{24}$ 32-bit words per proof. Unified has two windows of $2^{25}$ bytes per chunk. With identifiers below 64, unified covers windows below $2^{31}$ bytes; unrolled covers the $2^{32}$-byte range.
- **Unified capacity:** each circuit has $2^{23}$ rows but is charged $2^{24}$ cycles by the participant bound.

> **Algorithm 12 — SelectParameters**
>
> **Input:** fixed circuit description $C$, chunk role (instruction, standalone IT or delegation), profile, mode and commitment-config. **Output:** commitment layout and GKR/WHIR parameters. All values below are fixed before proof messages are read.
>
> 1. From $C$, set $n=\log_2(\mathrm{trace\ rows})$, memory/witness/committed-setup widths $(c_M,c_W,c_S)$ and the GKR layer relations. Use only the circuit families selected by Algorithm 2.
> 2. Select the parameter row below. For merged-feeder instruction chunks, require unified continuation mode and $n=23$; select feeder. Otherwise select ordinary by $n\in\{20,21,22,23,24\}$. Standalone IT and delegation chunks always select ordinary. Unsupported combinations have no verifier instance.
> 3. Set cap size to 16 hashes. For ordinary, use nonempty column groups $(M,W,S)$; for feeder, use $(M\mathbin{\|}W,S)$. Their widths fix the number of cap groups and the column order within each leaf. Batch claims in memory/witness/setup order.
> 4. For each round $r$, set $m_r=n-\sum_{i<r}k_i$, $|D_r|=2^{m_r}L_r$, leaf values per column to $2^{k_r}$ and path depth to $\log_2|D_r|-k_r-4$. Base leaves contain that many BabyBear values per column; later leaves contain $2^{k_r}$ extension-field coefficients. Use the fixed domain generator and tree ordering. Admit only configurations with power-of-two domains, $L_r\ge2$, $1\le k_r\le m_r$, $2^{k_r+4}\le|D_r|\le2^{27}$, $m_r-k_r\ge4$ before intermediate commitments, and $1\le n-\sum_r k_r$. Set the final coefficient count to $2^{n-\sum_r k_r}$.
> 5. Set $\ell=c_M+c_W+c_S$ and $D_{\mathrm{lookup}}=(a2^n+T)\max(1,c_S)$, where $a$ counts lookup accesses per row and $T$ counts committed-table entries plus the $2^{16}$ range table and $2^{19}$ timestamp table when used. With $B(x)=\lceil\log_2\max(1,x)\rceil$, select:
>
>    $$
>    \begin{aligned}
>    \ell_{\mathrm{lookup}}&=\max(0,100-\max(0,123-B(D_{\mathrm{lookup}}))) \\
>    \ell_{\mathrm{batch}}&=\max(0,100-\max(0,123-n-\log_2L_0-B(\ell)))
>    \end{aligned}
>    $$
>
> 6. Return the selected layout, schedules, sizes and PoW thresholds to Algorithms 3 and 7.
>
> **Parameter rows:** $L=(L_0,L_1,\ldots)$ lists base then intermediate expansion factors; $k,t,b$ list folds, query counts and PoW bits per round.
>
> | Family | $n$ | $k$ | $L$ | $t$ | $b$ |
> |---|---|---|---|---|---|
> | Ordinary | 20 | (1,5,5,4,4) | (2,256,8192,32768,524288) | (89,11,7,6,5) | (26,27,25,25,21) |
> | Ordinary | 21 | (1,5,5,5,4) | (2,64,2048,32768,524288) | (89,15,8,6,5) | (26,25,27,25,21) |
> | Ordinary | 22 | (1,5,5,5,5) | (2,64,2048,32768,524288) | (89,15,8,6,5) | (26,25,27,25,21) |
> | Ordinary | 23 | (1,5,5,5,4) | (2,16,512,16384,524288) | (89,23,10,7,5) | (26,24,25,19,21) |
> | Ordinary | 24 | (1,5,5,5,4,3) | (2,16,512,16384,524288,524288) | (89,23,10,7,5,5) | (26,24,25,19,21,21) |
> | Feeder | 23 | (1,5,5,5,4) | (16,32,1024,32768,1048576) | (21,17,9,5,4) | (29,26,25,26,21) |

For unrolled memory, assuming Algorithm 2's charges bound the memory-event counts:

$$
\begin{aligned}
N &\le 4\sum_f n_f2^{\ell_f} + \sum_d n_dA_d + 8n_{\mathrm{IT}}2^{24} + 33 \\
  &\le (2^{40}-1) + 2^{30} + 33 \\
\varepsilon_{\mathrm{mem}} &\le N\mu < 2^{-81.65}
\end{aligned}
$$

This is the algebraic bound before computational PoW accounting. The 33 boundary events are the ordinary registers and PC. A unified bound must include its authenticated IT products.

**Composed error.** Under the component assumptions, for $d$ proved statement invocations:

$$
\begin{aligned}
\varepsilon_{\mathrm{stmt}} &\le \varepsilon_{\mathrm{mem}} + \sum_{\mathrm{chunks}}(\varepsilon_{\mathrm{lookup}} + \varepsilon_{\mathrm{GKR}} + \varepsilon_{\mathrm{PCS}}) \\
\varepsilon_{\mathrm{alg,total}} &\le \sum_{\ell=1}^d \varepsilon_{\mathrm{stmt},\ell} + \varepsilon_{\mathrm{chain}} + \varepsilon_{\mathrm{terminal}}
\end{aligned}
$$

**References:** [GKR](https://people.cs.georgetown.edu/jthaler/GKRNote.pdf), [LogUp](https://eprint.iacr.org/2022/1530), [GKR lookup compression](https://eprint.iacr.org/2023/1284), [WHIR](https://eprint.iacr.org/2024/1586), [Two Shuffles Make a RAM](https://eprint.iacr.org/2023/1115).

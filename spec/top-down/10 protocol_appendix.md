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
> **Proof of work (PoW).** When challenge drawing requires $b$ bits of proof of work, the Prover supplies a 64-bit nonce, which is absorbed into the transcript immediately before drawing. The first drawn 32-bit word is reserved for PoW: the Verifier accepts only if it has $b$ leading zero bits. Field challenges are sampled from subsequent drawn words. For such PoW-gated draws and when $b=0$, the nonce is still absorbed and the first drawn word is still reserved, but every nonce passes; ungated challenge draws do not perform this PoW step.
>
> **Transcript flow across the proof.** `FullStatement` first absorbs the final state (register values, PC and timestamps) and all chunks' memory commitments (Merkle tree caps), with circuit-family identifiers and RAM initialization/teardown window identifiers. These identify the circuit types and RAM ranges associated with the commitments. Before absorbing a Merkle-cap sequence, it zero-pads to the next block boundary; successive absorb calls otherwise concatenate without padding. This precommitment binds the selected memory events before the shared challenges $\mathbf{r}_{\mathrm{mem}}$ are drawn (Algorithms 1–2).
>
> Each chunk starts a fresh transcript by absorbing its window identifiers, $\mathbf{r}_{\mathrm{mem}}$, and commitments to its setup, memory and remaining witness, omitting absent witness groups (Algorithm 3). Chunk transcripts proceed in parallel through GKR and WHIR; in the end, chunks' verified memory products are combined without further challenges.
>
> Prover prepares the memory commitments and computes the shared challenges before emitting the proof. Verifier reconstructs the memory transcript during `VerifyChunks` and authenticates the supplied challenges afterward.
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
> Prover and Verifier use common values for the following parameters, fixed throughout the protocol:
>
> - $\mathrm{profile}\in\{\mathrm{unrolled},\mathrm{unified}\}$. Unrolled uses separate instruction-family circuits; unified uses one combined instruction-family circuit (delegation circuits stay separate).
> - $\mathrm{mode}\in\{\mathrm{base},\mathrm{continuation}\}$. Base starts a new program-history chain and is meant for proving application execution; continuation validates and continues an incoming chain and is meant for proving recursive Verifier execution.
> - $\mathrm{commitment\text{-}config}\in\{\mathrm{ordinary},\;\mathrm{merged\text{-}feeder}\ \text{if}\ \mathrm{profile}=\mathrm{unified}\land\mathrm{mode}=\mathrm{continuation}\}$: ordinary uses separate Merkle trees for memory and remaining-witness columns; merged-feeder commits both column groups under one shared Merkle tree. The two options further impose restrictions on the WHIR (Algorithm 7) trace dimensions, LDE ratios, query counts, and PoW grinding difficulties selected for instruction circuits by Algorithm 12. Delegation circuits select their ordinary circuit-specific parameters independently of this setting.
>
> **Protocol**
>
> 1. Prover sends `ProgramSetupCaps`, one program-dependent setup cap per instruction family selected by $\mathrm{profile}$ and $\mathrm{mode}$ (Algorithm 12), followed by the final RISC-V register values $x_0..x_{31}$ and timestamp limbs, then PC and timestamp limbs. The claimed final state contains 99 raw 32-bit words:
>
>    $$
>    \mathrm{fin}=\bigl((x_j,\mathrm{ts}_{j,\mathrm{lo}},\mathrm{ts}_{j,\mathrm{hi}})_{j=0}^{31},(\mathrm{pc},\mathrm{ts}_{\mathrm{pc},\mathrm{lo}},\mathrm{ts}_{\mathrm{pc},\mathrm{hi}})\bigr).
>    $$
>
>    Both parties initialize the memory transcript $T_{\mathrm{mem}}$ by absorbing $\mathrm{fin}$ in the order above, then zero-pad to fill the current input block (13 words). Verifier requires $x_0=0$.
> 2. Prover calculates and sends the claimed shared challenges:
>
>    $$
>    \mathbf{r}_{\mathrm{mem}}=(r_{\mathrm{mem},0},\ldots,r_{\mathrm{mem},5},r_{\mathrm{mem},\eta})\in E^7
>    $$
>
> 3. Run $\operatorname{VerifyChunks}(\mathtt{ProgramSetupCaps},\mathbf r_{\mathrm{mem}},T_{\mathrm{mem}})$ (Algorithm 2), obtaining the read/write products $\mathrm{RS},\mathrm{WS}\in E$ and the completed memory transcript $T_{\mathrm{mem}}$.
> 4. Prover sends the 64-bit memory-PoW nonce. Both parties absorb it into $T_{\mathrm{mem}}$, draw one 32-bit PoW word, then sample the shared challenges from subsequent words. Verifier requires at least 19 leading zero bits in the PoW word and equality between the sampled challenges and the supplied $\mathbf r_{\mathrm{mem}}$.
> 5. Run $\operatorname{CloseMemory}(\mathrm{fin},\mathbf{r}_{\mathrm{mem}},\mathrm{RS},\mathrm{WS})$ (Algorithm 9).
> 6. Return $\operatorname{FinishChain}(\mathtt{ProgramSetupCaps},\mathrm{fin},\mathrm{mode})$ (Algorithm 10): the application result $x_{10},\ldots,x_{17}$ and program-history digest $h_0,\ldots,h_7$, each eight 32-bit words. Reject if any check or subalgorithm fails.
>
> **Soundness — conditional composition (adapted).** Assume commitment binding, Algorithm 2's participant-binding lemma, and Algorithm 9's event-encoding and execution-reconstruction premises. Outside the chunk-verification failure events, all accepted chunks satisfy their local relations and export the correct selected memory-event products. Participant binding fixes the event multisets before memory-challenge sampling; step 4 authenticates the supplied challenges against that transcript. Algorithm 9 then bounds acceptance of unequal read/write multisets by $\varepsilon_{\mathrm{mem}}\le N\mu$. If the multisets are equal, their boundary conditions and the local relations jointly imply an execution ending at $\mathrm{fin}$. Thus false execution acceptance requires a chunk-verification failure or a memory-fingerprint collision, giving
>
> $$
> \varepsilon_{\mathrm{exec}}\le\varepsilon_{\mathrm{mem}}+\sum_i\varepsilon_{\mathrm{chunk},i}.
> $$
>
> Here $\varepsilon_{\mathrm{chunk},i}$ includes all local lookup, GKR and PCS errors of Algorithm 3, counted once, with the sum bounded over permitted participant collections. Each component bound must hold for adversarial choices conditioned on the preceding transcript and no earlier soundness failure. The resulting execution claim is relative to the supplied setup identities; Algorithms 10–11 bind the program history and anchor the recursive executions to the expected program identities and successful endpoints.
>
> These component bounds enter the whole-system Fiat–Shamir analysis described in the final soundness section.

---

> **Algorithm 2 — VerifyChunks**
>
> **Configuration:** $\mathrm{profile}$, $\mathrm{mode}$ and $\mathrm{commitment\text{-}config}$ from Algorithm 1 fix the circuit families, their order, delegation setups and proof parameters.
>
> **Input:** `ProgramSetupCaps`, supplied $\mathbf{r}_{\mathrm{mem}}$ and the running memory transcript $T_{\mathrm{mem}}$ initialized with $\mathrm{fin}$. **Output:** accumulated read/write products $\mathrm{RS},\mathrm{WS}\in E$ and $T_{\mathrm{mem}}$ extended with the participating memory commitments and identifiers.
>
> **Verification**
>
> 1. Select the instruction families from Algorithm 12. Process unrolled instruction families followed by standalone IT, or unified instruction chunks, then the delegation families in the fixed order listed with the circuit parameters. For merged-feeder, require unified continuation $\mathrm{mode}$. Initialize $\mathrm{RS}\leftarrow1$, $\mathrm{WS}\leftarrow1$.
> 2. For each family in the configured order, Prover sends a chunk count followed by that many proofs. For unified, Prover sends the total chunk count and the number of trailing IT-carrying chunks before the proofs. For each chunk:
>    1. Run Chunk (Algorithm 3) for the selected circuit and supplied $\mathbf{r}_{\mathrm{mem}}$, obtaining its products, memory caps, setup caps and window identifiers $b$.
>    2. Require each instruction setup cap to match its family in `ProgramSetupCaps`; every unified chunk must match `ProgramSetupCaps[0]`. Delegation setup caps must match the Verifier's fixed cap for that type; standalone IT has no setup cap.
>    3. Both parties extend $T_{\mathrm{mem}}$ with the chunk's memory caps and window identifiers, using the fixed 32-bit family labels from Algorithm 12. Each identifier group is zero-padded to fill the current input block; memory-cap sequences begin at a block boundary:
>       - **Unrolled instruction or delegation:** the family-identifier block before the first chunk of each nonempty family, followed by the memory caps in proof order.
>       - **Standalone IT:** the IT family-identifier block before the first chunk, then each chunk's memory cap followed by a block of its eight window identifiers.
>       - **Unified instruction:** for each chunk, one block containing the unified-family identifier and its two window identifiers, then its memory cap.
>    4. Multiply the verified ordinary read/write products into $\mathrm{RS},\mathrm{WS}$.
>    5. For a trailing IT-carrying unified chunk, require its additional IT pair and multiply it into $\mathrm{RS},\mathrm{WS}$. Exclude this pair for leading unified chunks.
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
> 5. Return $\mathrm{RS},\mathrm{WS},T_{\mathrm{mem}}$.
>
> **Soundness — participant/window binding (new, conditional).** Required participant-binding lemma: under commitment binding, for each fixed memory-transcript prefix immediately before the nonce, all completions satisfying the local chunk relations and participant checks induce the same selected read/write event multisets, including multiplicities and Algorithm 9's boundary events, independently of the subsequently sampled memory challenges. Its proof must establish that the encoding fixes the participating caps and their interpretation sufficiently to determine these multisets. In particular, proof counts, `ProgramSetupCaps` and separate witness caps are omitted from this prefix: varying them while preserving the prefix must not change event selection, tuple values or multiplicities. Later absorption of setup/witness caps into chunk transcripts does not establish this earlier binding. This lemma remains a proof obligation.
>
> Outside local verification failures, setup-cap equality ties instruction chunks to the supplied program setups and delegation chunks to the fixed delegation setups. Circuit-bound, strictly increasing IT windows exclude repeated initialization/teardown windows; complete coverage remains a premise of Algorithm 9's reconstruction lemma. The capacity argument must additionally show that the charged counts bound all selected events, including IT and boundary events in the final $N$ bound. Subject to these obligations, the accumulated products are fingerprints of the fixed multisets, so Algorithm 9's collision bound applies after Algorithm 1 authenticates the shared challenges.

---

> **Algorithm 3 — Chunk**
>
> **Input:** selected circuit $C$, chunk role, $\mathrm{commitment\text{-}config}$ and shared $\mathbf{r}_{\mathrm{mem}}$. **Prover data:** column tables $M,W,S$ and intermediate gate values; lookup multiplicities belong to $W$. **Relation:** $C$'s gates/zero constraints and selected lookup memberships hold; exported products equal the selected memory-event products. **Output:** verified products, `MemoryCaps`, `SetupCaps` and window identifiers $b$.
>
> **Notation:** $C$ is the compiled arithmetic circuit selected by the Verifier, on $2^n$ rows. Its wiring, zero constraints, column order, lookup tables and auxiliary relations are fixed public parameters; Algorithm 12 selects the proof parameters and maps the memory, remaining-witness and setup columns $M,W,S$ to their cap groups. Virtual setup tables are evaluated directly by the Verifier; $\operatorname{MLE}(A)$ is table $A$'s multilinear extension.
>
> 1. Run SelectParameters (Algorithm 12) for $C$, its role and $\mathrm{commitment\text{-}config}$. Prover sends $b$, followed by the cap groups in setup/memory/witness order, omitting groups absent from the selected layout. The layout fixes their counts, sizes and column grouping. The window identifiers $b$ are 32-bit indices of RAM initialization/teardown ranges: eight for standalone IT, two for unified instructions, and none for other chunks; range sizes are listed with the circuit parameters.
>
>    The witness $W$, including multiplicities, is fixed at this point; in merged-feeder instruction chunks it was already committed before $\mathbf r_{\mathrm{mem}}$. Both parties start a fresh transcript $T$ by absorbing the ordered prefix below, omitting cap groups absent from the configured layout:
>
>    $$
>    b\mathbin{\|}\mathbf{r}_{\mathrm{mem}}\mathbin{\|}\mathtt{SetupCaps}\mathbin{\|}\mathtt{MemoryCaps}\mathbin{\|}\mathtt{WitnessCaps}
>    $$
>
>    Each chunk initializes independently from this prefix; no memory-transcript seed is inherited.
> 2. Prover sends the lookup-PoW nonce. Verifier checks the lookup-PoW threshold from Algorithm 12; both parties draw $(\alpha,\beta)\in E^2$.
> 3. Prover evaluates $C$ forward, accumulates outputs to sixteen entries and sends tables $A_0,\ldots,A_{s-1}$. Both parties absorb the tables, draw $(u_0,\ldots,u_3,\lambda)$ and set $a_j\leftarrow\operatorname{MLE}(A_j)(u)$.
> 4. For $k=4,\ldots,n-1$, run GKRLayer (Algorithm 5) for the compression layer on the current claims and batching challenge. Then run it for each main layer, from outputs towards inputs. Each call continues $T$ and returns the claims and batching challenge for the next layer; the last call yields the base-column claims $f_j(\zeta)=a_j$.
> 5. Prover sends the batching/proximity-PoW nonce. Verifier checks the batching-PoW threshold from Algorithm 12; both parties draw $\gamma\in E$.
> 6. Run $\operatorname{OutputChecks}(A_0,\ldots,A_{s-1})$ (Algorithm 6), obtaining the memory-product pairs.
> 7. Run $\operatorname{WHIR}(\mathrm{base\ caps},\zeta,a,\gamma,T)$ (Algorithm 7). Return the products, `MemoryCaps`, `SetupCaps` and $b$.
>
> WHIR continues the GKR transcript. These BabyBear instances are unpacked. For packed instances, both parties draw fresh pack coordinates after the main layers, merge claims within each commitment set by multilinear weights, and append the coordinates to $\zeta$ before the batching PoW.
>
> **Soundness — local composition (adapted, conditional).** Fix the circuit, layout and shared memory challenges. Assume binding commitments, the layer-reduction premises of Algorithm 5 and the opening guarantee of Algorithm 7. Lookup tuples, selectors, tables and multiplicities must be determined by committed columns or public data before $\alpha,\beta$. Outside the GKR and PCS failure events, the supplied output tables are the circuit's actual outputs and its zero constraints hold. Algorithm 6 then establishes lookup membership, except with error $\varepsilon_{\mathrm{lookup}}$, and returns the selected memory products. Hence
>
> $$
> \varepsilon_{\mathrm{chunk}}\le\varepsilon_{\mathrm{GKR}}+\varepsilon_{\mathrm{PCS}}+\varepsilon_{\mathrm{lookup}}.
> $$
>
> Algorithm 5 owns the algebraic verification of the product/rational compression trees; Algorithm 6 owns the lookup fingerprint error; Algorithm 7 owns base-claim batching and opening verification. Algorithm 1 uses the resulting local relation with Algorithm 2's event binding and Algorithm 9's reconstruction premises. The displayed bound covers the unpacked BabyBear path; packed variants require an additional reduction for the pack-coordinate claim merge.

---

> **Algorithm 4 — EQSumcheck**
>
> **Input:** incoming point $u \in E^k$, batched claim $v$ for gate polynomial $G$ of individual degree $\le 2$, and the running chunk transcript $T$. **Output:** point $r$, scalar $v$ and last EQ factor $e$; the call updates $T$.
>
> **Notation:** $\operatorname{eq}(u,x) = \prod_j((1-u_j)(1-x_j)+u_jx_j)$, the Boolean-cube interpolation kernel.
>
> 1. Initialize $e \leftarrow 1$.
> 2. For each $j = 0,\ldots,k-1$:
>    1. Prover sends the coefficients of $g_j(X)$, with $\deg g_j \le 3$.
>    2. Verifier requires $e\,(g_j(0)+g_j(1)) = v$.
>    3. Both parties absorb the coefficients into $T$, then derive $r_j\in E$.
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
> **Soundness — Sumcheck and EQ factoring (adapted).** Assume $u$ and the polynomial $G$ are fixed before this call's challenges, $G$ has individual degree at most two, and every round polynomial is fixed before its evaluation challenge. For a false incoming claim and a nonzero carried EQ factor $e$, the endpoint check forces the sent cubic to differ from the honest round polynomial. That discrepancy vanishes at $r_j$ with probability at most $3\mu$. The new EQ factor is $1-u_j+(2u_j-1)r_j$: it is $1/2$ if $u_j=1/2$, and otherwise vanishes with probability at most $\mu$.
>
> Charging each potentially vanishing factor as an exceptional event, a false incoming sum reduces to a false final claim $v=eG(r)$ except with probability at most $\min(1,(3k+Z)\mu)$, where $Z\le k$. Algorithm 5 must establish the final gate evaluation through its input claims. It counts this reduction error once in its layer budget.

---

> **Algorithm 5 — GKRLayer**
>
> **Input:** output claims $(u,a)$, batching challenge $\lambda$, fixed circuit layer $C$ and the running chunk transcript $T$. **Output:** preceding-layer claims and the next batching challenge; the call updates $T$.
>
> **Notation:** `Batch` uses $C$'s power order in $\lambda$ and includes claim $0$ for every zero constraint. `Gate` is the same batched gate expression, evaluated by the Verifier.
>
> 1. Set $v\leftarrow\operatorname{Batch}(a\text{ and zero claims};\lambda)$; obtain $(r,v,e)\leftarrow\operatorname{EQSumcheck}(u,v,T)$ (Algorithm 4) for the batched gate polynomial.
> 2. **Compression layer:**
>    1. Prover sends $h_j(0,r),h_j(1,r)$ for every required input.
>    2. Verifier requires $v=e\,\operatorname{Gate}(\text{endpoint values};\lambda)$; both parties absorb all endpoints and draw $(t,\lambda')$.
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
>    3. Prover sends the additional evaluations required by $C$'s auxiliary polynomial relations. Both parties absorb these together with the input evaluations and draw $\lambda'$.
>    4. Check $C$'s auxiliary relations and publicly evaluable setup polynomials. Return the preceding-layer claims at $r$ in $C$'s fixed input-polynomial order, and $\lambda'$.
>
> Compression gates: product $h_0h_1$; rational sum $(n_0d_1+n_1d_0,d_0d_1)$. The Verifier evaluates public setup polynomials directly; committed setup polynomials become WHIR opening claims.
>
> **Soundness — layer reduction and GKR budget (adapted, conditional).** Assume the fixed layer wiring and auxiliary identities implement the claimed gate relation, its batched gate polynomial satisfies Algorithm 4's degree bound, and each claimed value is fixed before the challenge testing it. Algorithm 4 reduces a false batched output claim to a false gate evaluation. The gate check then forces a false preceding-layer claim; auxiliary and public-polynomial checks must establish the identities used in this implication. In a compression layer, fixed endpoint discrepancies define a nonzero linear polynomial in $t$, so interpolation hides them with probability at most $\mu$. Induction through the layers terminates at the base openings established by Algorithm 7.
>
> For the complete GKR path in Algorithm 3, a false sixteen-entry output table survives evaluation at $u\in E^4$ with probability at most $4\mu$; batching $b$ fixed scalar claims costs at most $(b-1)\mu$. Let $B$ be the sum of all power-batching degrees, including the initial output batch; $R$ the total number of EQSumcheck rounds; $Z\le R$ the charged EQ-zero events; and $S$ the sum of the remaining point/line-test degrees, including endpoint interpolation. Then
>
> $$
> \varepsilon_{\mathrm{GKR}}\le\min(1,\mu(4+B+3R+Z+S)).
> $$
>
> For $L$ main layers each using $n$ rounds, $R=\sum_{k=4}^{n-1}k+Ln$. These are proof-accounting quantities determined by the selected circuit. Completing the bound requires the layer/auxiliary-relation induction and explicit $B,R,Z,S$ counts for that circuit; lookup fingerprinting and base-opening errors are composed in Algorithm 3.

---

> **Algorithm 6 — OutputChecks: memory products and LogUp**
>
> **Input:** original sixteen-entry tables. **Output:** ordinary and any embedded-IT read/write product pairs, after checking the lookup identities.
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
> **Soundness — lookup membership and product export (adapted, conditional).** Assume Algorithms 5 and 7 authenticate the output tables as evaluations of the product/rational compression trees. Also assume tuple encoding is injective, all lookup tuples and multiplicities are fixed before $\alpha,\beta$, and every invalid tuple occurring in the queries has a nonzero count modulo $p$. An invalid tuple then contributes an uncancelled pole to the symbolic rational difference. Clearing denominators gives a nonzero polynomial in $\alpha,\beta$; the authenticated $D\ne0$ check permits this reduction on accepted proofs. If category $a$ has $T_a$ fraction occurrences and tuple width $w_a$, its numerator has total degree at most $D_a\le T_a\max(1,w_a)$. Therefore
>
> $$
> \varepsilon_{\mathrm{lookup}}\le\min\!\left(1,\mu\sum_a D_a\right).
> $$
>
> This sum covers all categories sharing $\alpha,\beta$. Fewer than $p$ query occurrences per category suffices for the nonzero-count premise; the actual per-circuit query bounds and numerator degrees remain to be established. The returned memory products are exact products of the authenticated output entries; Algorithm 9 tests their global equality. Compression-tree verification is charged to Algorithm 5.

---

> **Algorithm 7 — WHIR**
>
> **Input:** base cap hashes; claims $f_j(\zeta)=a_j$; $\gamma$; the chunk transcript $T$ continued after GKR and batching. **Parameters:** oracle layout, domains, fold/query schedule and PoW thresholds from Algorithm 12. **Prover data:** base and folded polynomials and Merkle trees. **Relation:** the committed base polynomials have the claimed evaluations and required encoding/degree bounds. **Output:** acceptance of the base-opening claims; the call continues $T$.
>
> **Notation:** $f_j$ are column MLEs and $\zeta$ their opening point. For monomial coefficients $c_t$, $F_f(X)=\sum_t c_tX^t$ and $\operatorname{powers}(s)=(s,s^2,s^4,\ldots)$, so $F_f(s)=f(\operatorname{powers}(s))$; low-index bits select the first folded variables. $\operatorname{eq}$ is the interpolation kernel from EQSumcheck; $w$ is the running weight function, $m$ the remaining dimension and $D_r$ the current Reed–Solomon evaluation domain.
>
> 1. Prover batches $f$; Verifier initializes $v,w$:
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
>    1. Run QuadraticStep (Algorithm 8) $k_r$ times on the running claim, weights and $T$, obtaining fold challenges $a$ and restricting $f,w$.
>    2. Prover sets $f_{\mathrm{next}}\leftarrow f$ and sends a cap committing to it. Both parties absorb the cap into $T$ and draw $\xi$.
>    3. Prover sends $u$, claimed as $F_{\mathrm{next}}(\xi)$, followed by the 64-bit query-PoW nonce. Both parties absorb $u$ and the nonce into $T$; Verifier checks the $b_r$-bit PoW. Both parties draw query indices $I_0,\ldots,I_{t_r-1}$ uniformly from $[0,|D_r|/2^{k_r})$ with replacement (one index per fold group), then derive $\delta$ from fresh hash output beyond the query-index randomness.
>    4. For each query $j=0,\ldots,t_r-1$:
>       1. Prover sends current-oracle leaves and Merkle paths.
>       2. Verifier authenticates each leaf against its cap at the configured tree position and runs Fold (Algorithm 8) with the selected encoding, challenges $a$ and query coset points. For base oracles, Verifier combines the per-column folds with the same $\gamma$ powers used in step 1 to obtain $q_j$; later rounds fold the single batched oracle.
>       3. Set $s_j\leftarrow(\omega^{I_j})^{2^{k_r}}$, where $\omega$ generates the current oracle's domain.
>    5. Verifier updates:
>
>       $$
>       \begin{aligned}
>       w &\leftarrow w+\delta\,\operatorname{eq}(\operatorname{powers}(\xi),\cdot) \\
>         &\quad +\sum_{j=0}^{t_r-1}\delta^{j+2}\operatorname{eq}(\operatorname{powers}(s_j),\cdot) \\
>       v &\leftarrow v+\delta u+\sum_{j=0}^{t_r-1}\delta^{j+2}q_j
>       \end{aligned}
>       $$
>
>    6. Continue with $f\leftarrow f_{\mathrm{next}}$ and its commitment as the next round's oracle.
> 3. Final round:
>    1. Run QuadraticStep $k_r$ times, continuing the same claim, weights and $T$.
>    2. Prover sends exactly $2^{n-\sum_r k_r}$ monomial coefficients $c$ of the remaining polynomial.
>    3. Prover sends the 64-bit final query-PoW nonce. Both parties absorb $c$ and the nonce into $T$; Verifier checks the final PoW. Both parties draw the final query indices as in step 2.3.
>    4. Prover sends the current-oracle leaves and Merkle paths. Verifier authenticates the leaves and runs Fold, defining $s_j$ as in step 2.4. For each query require $q_j=\sum_l c_l s_j^l$.
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
> **Soundness — opening reduction (adapted, conditional).** Assume binding commitments, Algorithm 8's encoding/restriction identities, and a Reed–Solomon proximity/list-decoding theorem applicable to the selected domains, both leaf encodings and this accumulator update. That theorem must supply candidate lists at the required challenge boundaries and bound the probability of leaving the candidate invariant. Outside those failures, the following tests propagate a false base-opening claim to rejection at the final polynomial check:
>
> - **Base batching:** for $c$ columns and claims fixed before $\gamma$, cancellation of a nonzero discrepancy costs at most $(c-1)\mu$.
> - **Claim reduction:** each QuadraticStep costs at most $2\mu$ by Algorithm 8. Each $\delta$ combination has degree at most $t_r+1$ and costs at most $(t_r+1)\mu$, provided all combined discrepancies are fixed before $\delta$. Commitment binding fixes the queried leaf values even when their paths are supplied later.
> - **OOD separation:** two distinct candidate polynomials fixed before $\xi$, with difference of degree at most $d_r$, agree at $\xi$ with probability at most $d_r\mu$. The proximity reduction must specify which candidate comparisons are needed and account for their number.
> - **Query consistency:** for fixed fold challenges and a candidate fixed before the query draw, let $a$ be its agreement fraction with the authenticated fold over the current fold groups. Sampling $t_r$ indices independently with replacement accepts this candidate with probability $a^{t_r}$. For a predetermined candidate list, sum these bounds over the false candidates tested.
>
> With each failure charged once, the algebraic opening budget is
>
> $$
> \varepsilon_{\mathrm{PCS}}\le\varepsilon_{\mathrm{batch}}+\varepsilon_{\mathrm{proximity/list}}+\varepsilon_{\mathrm{OOD}}+\varepsilon_{\mathrm{query}}+\varepsilon_{\mathrm{combine}}+\varepsilon_{\mathrm{quadratic}}.
> $$
>
> Instantiating the proximity invariant, candidate-list sizes and fold-group agreement bounds for every round remains a proof obligation. The final coefficient and accumulator checks close the reduction once that invariant is established. Commitment binding and Fiat–Shamir compilation enter the separate computational analysis.

---

> **Algorithm 8 — QuadraticStep and Fold**
>
> **Notation:** $a=(a_0,\ldots,a_{k-1})$ are fold challenges; $c_b$ are authenticated local monomial coefficients. $x$ is a nonzero coset point; $F_f$ is the univariate encoding of $f$. The $\kappa$ values are weights of restricted EQ terms.
>
> **QuadraticStep**
>
> **Input:** running claim $v$, weights $w$ and transcript $T$; Prover holds the current polynomial $f$. **Output:** fold challenge $a$; the call restricts $f,w$, updates $v$ and continues $T$.
>
> 1. Prover sends three coefficients of $h(X)$, with $\deg h\le 2$, claiming $h(X)=\sum_x f(X,x)w(X,x)$.
> 2. Verifier requires $h(0)+h(1)=v$; both parties absorb its coefficients into $T$ and draw $a$.
> 3. Prover restricts $f$; Verifier updates $v,w$:
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
> **Fold**
>
> **Input:** authenticated leaf values, fold challenges $a$, the round's encoding from WHIR and, for evaluation leaves, the query's coset points. **Output:** folded value $q$.
>
> **Coefficient leaves:**
>
> 1. Return:
>
>    $$
>    \sum_{b\in\{0,1\}^k}c_b\prod_{j=0}^{k-1}a_j^{b_j}
>    $$
>
> **Evaluation leaves:**
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
> **Soundness — quadratic reduction and exact folding (adapted).** For QuadraticStep, assume $f$ and $w$ are multilinear and fixed before the fresh challenge. The honest round polynomial has degree at most two. If the incoming sum claim is false, the endpoint check forces a nonzero discrepancy of degree at most two; it vanishes at $a$ with probability at most $2\mu$. Thus a false incoming claim reduces to a false restricted claim except with this error, which Algorithm 7 counts once per step.
>
> For Fold, assume authenticated leaves have the specified encoding and coset/bit ordering, with nonzero coset points. Evaluating the local coefficient tensor restricts the corresponding multilinear coordinates. For evaluation leaves, write $F(X)=F_{\mathrm{even}}(X^2)+XF_{\mathrm{odd}}(X^2)$: the displayed formula returns $F_{\mathrm{even}}(x^2)+a_jF_{\mathrm{odd}}(x^2)$, the same coordinate restriction. Iteration gives the folded evaluation used by Algorithm 7. These deterministic identities require the layout-to-polynomial correspondence for each encoding.
>
> Restricting each EQ term contributes its evaluated leading factor to its weight $\kappa$. The final cube sum is therefore $\kappa_0 f_{\mathrm{final}}(\zeta_{\mathrm{remaining}})+\sum_j\kappa_jF_{\mathrm{final}}(s_j)$, with each OOD/query scalar squared at every subsequent coordinate restriction. This identity justifies Algorithm 7's final accumulator evaluation; the encoding correspondence remains an implementation-specific proof obligation.

---

> **Algorithm 9 — CloseMemory**
>
> **Input:** final state $\mathrm{fin}$, $\mathbf{r}_{\mathrm{mem}}$, authenticated products $\mathrm{RS},\mathrm{WS}$.
>
> **Notation:** $R,W$ are read/write event multisets; $\mathbf{r}_{\mathrm{mem}}=(r_{\mathrm{mem},0},\ldots,r_{\mathrm{mem},5},r_{\mathrm{mem},\eta})$. In event $t=(a,t_0,\ldots,t_5)$, the limbs are address lo/hi, timestamp lo/hi, value lo/hi; tags are 0 = register, 1 = RAM, 2 = PC. Define $L_{\mathbf{r}_{\mathrm{mem}}}(t)=a+r_{\mathrm{mem},\eta}+\sum_{j=0}^5r_{\mathrm{mem},j} t_j$ with six independent coefficients.
>
> 1. Form multisets of event tuples: `Initial` contains the ordinary-register writes $x_0,\ldots,x_{31}$ of value 0 at time 0, and the PC write with value 0 at time 4; `Final` contains the 32 register reads and PC read specified by $\mathrm{fin}$. Include their boundary factors:
>
>    $$
>    \begin{aligned}
>    \mathrm{WS} &\leftarrow \mathrm{WS}\prod_{t\in\mathrm{Initial}}L_{\mathbf{r}_{\mathrm{mem}}}(t) \\
>    \mathrm{RS} &\leftarrow \mathrm{RS}\prod_{t\in\mathrm{Final}}L_{\mathbf{r}_{\mathrm{mem}}}(t)
>    \end{aligned}
>    $$
>
> 2. Require $\mathrm{RS}=\mathrm{WS}$. RAM boundaries already enter through IT products.
>
> Chunk transcripts end independently. This product equality uses the shared $\mathbf{r}_{\mathrm{mem}}$ and requires no further challenges or transcript merge.
>
> **Soundness — memory fingerprint (conditional).** Assume Algorithm 2 fixes $R,W$, including the boundary events, before the shared challenges are sampled, and the event encoding is injective on accepted data. If $R\ne W$, unique factorization makes the difference of their products nonzero: each affine factor has $r_{\mathrm{mem},\eta}$-coefficient 1, fixing its normalization. This difference has total degree at most $N=\max(|R|,|W|)$, so acceptance of unequal multisets has probability $\varepsilon_{\mathrm{mem}}\le\min(1,N\mu)$. Algorithm 1 charges this error once per statement, using a capacity bound that includes all instruction, delegation, IT and boundary events. Accepted-boundary injectivity, particularly for timestamp limbs reduced modulo $p$, remains a proof obligation. The reconstruction argument below supplies the execution interpretation of multiset equality.
>
> **Soundness — execution reconstruction (adapted/new).** Required reconstruction lemma: assume the following properties of the accepted chunks and their combined events:
>
> - **Local semantics:** instruction and delegation relations hold under the supplied program setups and fixed delegation setups, including instruction decoding, lookup membership and local PC updates. Range constraints give addresses, values and timestamps their intended integer interpretation; inactive rows contribute neutral memory products.
> - **Memory consistency:** the read/write event multisets, including boundary events, are equal with multiplicity under the injective encoding above. Timestamps strictly increase along each location's state transitions, and each read identifies a unique preceding write by location and timestamp.
> - **Boundary coverage:** register and PC boundary events are exactly those in steps 1–2. Disjoint IT windows cover every RAM location used by the execution and supply its zero-valued initialization and matching teardown.
> - **Global connectivity:** PC events connect all active instruction transitions into a single chain from the initial PC/time to the final PC/time in $\mathrm{fin}$. Delegation requests and responses match with multiplicity, including their operation identities, arguments and results.
>
> These premises imply an execution of the program identified by the supplied setups, from $(\mathrm{pc},\mathrm{time})=(0,4)$ and zero ordinary registers/RAM to $\mathrm{fin}$. Proving this implication and deriving its premises from the accepted circuit and participant checks remain reconstruction proof obligations.

---

> **Algorithm 10 — FinishChain**
>
> **Input:** program setups `ProgramSetupCaps`, final state $\mathrm{fin}$ and base/continuation $\mathrm{mode}$. **Output:** application result $y$ and program-history digest $h$, each eight 32-bit words.
>
> **Notation:** $x_j$ and $\mathrm{pc}$ come from $\mathrm{fin}$; `Hash` uses the transcript's seven-round BLAKE2s and word encoding.
>
> 1. Set $y\leftarrow(x_{10},\ldots,x_{17})$ and:
>
>    $$
>    e\leftarrow\operatorname{Hash}\bigl((\mathrm{pc},0^{15})\mathbin{\|}\mathtt{ProgramSetupCaps}\bigr)
>    $$
>
>    After PC, `Hash` zero-pads to fill the current input block (15 words), then absorbs the ordered setup caps. Timestamps are excluded.
> 2. **Base mode:** require $(x_{18},\ldots,x_{25})=0^8$; set $h\leftarrow\operatorname{Hash}(0^8\mathbin{\|}e)$.
> 3. **Otherwise, continuation mode:**
>    1. Set $h_{\mathrm{in}}\leftarrow(x_{18},\ldots,x_{25})$.
>    2. Prover sends the 16-word hash-chain preimage $(h_{\mathrm{prev}},e_{\mathrm{prev}})$, eight 32-bit words each. Verifier requires $\operatorname{Hash}(h_{\mathrm{prev}}\mathbin{\|}e_{\mathrm{prev}})=h_{\mathrm{in}}$.
>    3. **If $e_{\mathrm{prev}}=e$:** set $h\leftarrow h_{\mathrm{in}}$.
>    4. **Otherwise:** set $h\leftarrow\operatorname{Hash}(h_{\mathrm{in}}\mathbin{\|}e)$.
> 4. Return $(y,h)$.
>
> **Soundness — program-history binding (conditional).** Assume binding of the encoded setup/ending-PC identities and hash-chain nodes. In continuation mode, assume authenticated execution of the intended Verifier returns the genuine child result and history $(y,h_{\mathrm{in}})$. The base case starts the history with the current identity $e$. In continuation mode, the checked preimage identifies the incoming history's last identity: equality with $e$ preserves the history, while inequality appends $e$. Induction therefore binds $h$ to the sequence of identities with consecutive repetitions collapsed. Algorithm 11 supplies the authenticated handoffs and compares this history with the expected one. Charge failures of identity/node binding once to $\varepsilon_{\mathrm{chain}}$ in the computational analysis; recursion depth and work use the external bound in Algorithm 11.

---

> **Algorithm 11 — Recursion and terminal acceptance**
>
> **Public claim:** application identity, expected collapsed Verifier history and result $y$. **Witness:** child proof bundle and its Verifier-execution trace. **Recursive relation:** the selected Verifier program runs `FullStatement` on the child and reaches its successful return with $(y,h)$ in $x_{10},\ldots,x_{25}$.
>
> 1. Prove the application execution:
>    - **If unrolled:** use unrolled circuits; verify with the base unrolled Verifier.
>    - **If unified:** use unified circuits; verify with the base unified Verifier.
> 2. Optionally repeat, proving the selected Verifier's execution:
>    - **If unrolled:** use unrolled circuits; verify with the unrolled continuation Verifier.
>    - **If unified:** use unified circuits; verify with the unified continuation Verifier.
> 3. **Bridge (if switching from unrolled to unified):** prove the selected unrolled base/continuation Verifier's execution with unified circuits; verify with the unified continuation Verifier, then repeat step 2 as needed using unified circuits.
> 4. **Terminal acceptance:**
>    1. Verify the last proof with `FullStatement`, obtaining $(y,h)$.
>    2. Require its `ProgramSetupCaps` and final PC to match the expected setup caps and successful ending PC, and require $h=h_{\mathrm{expected}}$.
>    3. Accept and expose $y$ only if all verification and expectation checks pass; otherwise reject.
>
> Expected identities and $h_{\mathrm{expected}}$ are determined by the application starting values and selected recursive configuration. The L1 route uses a merged-commitment feeder, then a packed Proth120 proof with a Keccak transcript, and must enforce the same expectation checks. Its serialization, public-claim mapping and contract linkage require a separate protocol.
>
> **Soundness — recursive composition (conditional).** Assume Algorithm 1's execution guarantee for every invoked configuration; binding and canonical interpretation of the history from Algorithm 10; and correctness of each selected Verifier program, including its child-input parsing, acceptance branch and transfer of $(y,h)$ to the designated registers. Expected setup identities, successful PCs and history must be fixed by the public claim. A recursive composition reduction must justify applying the component soundness bounds to child proofs carried inside execution witnesses, within an external bound $d$ on all proved invocations and their query/work budgets.
>
> Outside the corresponding failure events, terminal acceptance identifies a successful execution of the expected outer Verifier. Its verified local semantics imply child acceptance with the same result and the authenticated child history. Applying this implication at each handoff reaches the base application execution, so the exposed $y$ is its result. The algebraic error is bounded by the sum over all proved invocations; Algorithm 10 accounts for history binding, and terminal comparisons anchor the claimed identities and endpoints. Establishing the recursive reduction and each implementation handoff remains a proof obligation. Extending this argument to the stated L1 route additionally requires soundness of its terminal proof system and correctness of its serialization, public-claim mapping and contract linkage.

---

**Circuit and memory parameters.** Merkle caps contain sixteen 256-bit hashes. $\mathrm{profile}$ and $\mathrm{mode}$ fix the instruction-family selection in Algorithm 12; the families have the following row counts and capacity charges.

- **Unrolled instructions:** add/sub/LUI/AUIPC/MOP (family 1); jump/branch/compare (2); shift/binary (3); unsigned multiply/divide (4); word memory (16); subword memory (17). Trace logarithms are 24 except multiply/divide, which uses 23.
- **Delegations:** BLAKE2s, bigint, Keccak special5, theta/rho, column parity and chi5, with trace logarithms $(20,22,22,22,22,22)$ and charges $A_d=(44\cdot2^{20},20\cdot2^{22},15\cdot2^{22},17\cdot2^{22},15\cdot2^{22},13\cdot2^{22})$ in that order.
- **IT windows:** standalone IT has $2^{24}$ rows and eight windows of $2^{24}$ 32-bit words per proof. Unified has two windows of $2^{25}$ bytes per chunk. With identifiers below 64, unified covers windows below $2^{31}$ bytes; unrolled covers the $2^{32}$-byte range.
- **Unified capacity:** each circuit has $2^{23}$ rows but is charged $2^{24}$ cycles by the participant bound.

> **Algorithm 12 — SelectParameters**
>
> **Input:** fixed circuit description $C$, chunk role (instruction, standalone IT or delegation), $\mathrm{profile}$, $\mathrm{mode}$ and $\mathrm{commitment\text{-}config}$. **Output:** ordered instruction-family list, commitment layout and GKR/WHIR parameters. All layout choices and proof parameters below are fixed before proof messages are read.
>
> **Program setup caps (Algorithm 1):**
>
> | $\mathrm{profile}$ | $\mathrm{mode}$ | Instruction-family IDs, in order | Setup-cap count |
> |---|---|---|---|
> | Unrolled | Base | 1, 2, 3, 4, 16, 17 | 6 |
> | Unrolled | Continuation | 1, 2, 3, 16 | 4 |
> | Unified | Base or continuation | 128 (unified) | 1 |
>
> **Other family identifiers:** standalone IT uses 255. Delegation types BLAKE2s, bigint, Keccak special5, theta/rho, column parity and chi5 use their fixed CSR numbers: 0x7c7, 0x7ca, 0x7cb, 0x7cc, 0x7cd and 0x7ce, respectively.
>
> `ProgramSetupCaps` contains one cap per selected instruction family, including families with zero chunks. Neither its count nor its family list is sent in the proof. $\mathrm{commitment\text{-}config}$ does not change this selection.
>
> 1. Select the ordered instruction-family list from the table above and the other families from their fixed identifiers. From $C$, set $n=\log_2(\mathrm{trace\ rows})$, memory/witness/committed-setup widths $(c_M,c_W,c_S)$ and the GKR layer relations.
> 2. Select the parameter row below. For merged-feeder instruction chunks, require unified continuation $\mathrm{mode}$ and $n=23$; select feeder. Otherwise select ordinary by $n\in\{20,21,22,23,24\}$. Standalone IT and delegation chunks always select ordinary. Unsupported combinations have no Verifier instance.
> 3. Set cap size to 16 hashes. For ordinary, `MemoryCaps`, `WitnessCaps` and `SetupCaps` commit the nonempty groups $M,W,S$, respectively. For feeder, `MemoryCaps` commits $M\mathbin{\|}W$ and `SetupCaps` commits $S$. These groups fix the cap counts and the column order within each leaf. Batch claims in memory/witness/setup order.
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
> 6. Return the ordered instruction-family list to Algorithms 1–2 and the selected commitment layout, schedules, sizes and PoW thresholds to Algorithms 3 and 7.
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

**Soundness — parameter instantiation (conditional).** Algorithm 12 fixes the circuit and commitment layout, field domains and challenge/query schedule to which the preceding bounds apply. For each selected circuit, instantiate Algorithm 5's batching/round/test counts, Algorithm 6's occurrence and numerator-degree bounds, and Algorithm 7's proximity/list and agreement bounds. The lookup charge $D_{\mathrm{lookup}}$ must dominate the degree sum actually proved in Algorithm 6. The PoW thresholds enter the computational accounting of the protected tests; their instantiation must use the challenge-distribution bound $\mu$ and the corresponding algebraic degrees. In particular, the constant $123$ in step 5 must be reconciled with $-\log_2\mu\approx121.66$ for the stated sampling rule. These per-configuration checks remain proof obligations.

For unrolled memory, if Algorithm 2's charges bound all selected instruction/delegation events and each IT proof contributes at most $8\cdot2^{24}$ events on each side, then

$$
\begin{aligned}
N &\le 4\sum_f n_f2^{\ell_f} + \sum_d n_dA_d + 8n_{\mathrm{IT}}2^{24} + 33 \\
  &\le (2^{40}-1) + 2^{30} + 33 \\
\varepsilon_{\mathrm{mem}} &\le N\mu < 2^{-81.65}.
\end{aligned}
$$

The 33 boundary events are the ordinary registers and PC. This bounds the memory-fingerprint error in the algebraic model. The unified profile requires a separate event-count bound including its authenticated IT products.

**Composed error (conditional).** In the fresh-word algebraic model, assume the binding, encoding, reconstruction and recursive-composition premises above. For each statement, use Algorithm 3's chunk bound and Algorithm 9's memory bound. For an externally bounded collection of at most $d$ proved invocations,

$$
\begin{aligned}
\varepsilon_{\mathrm{stmt}} &\le \varepsilon_{\mathrm{mem}} + \sum_{\mathrm{chunks}}(\varepsilon_{\mathrm{lookup}} + \varepsilon_{\mathrm{GKR}} + \varepsilon_{\mathrm{PCS}}) \\
\varepsilon_{\mathrm{alg,total}} &\le \min\!\left(1,\sum_{\ell=1}^d \varepsilon_{\mathrm{stmt},\ell}\right).
\end{aligned}
$$

Each bound must hold under the preceding transcript and permitted adaptive choices, with sums bounded over the allowed participant collections. Algorithm 10's $\varepsilon_{\mathrm{chain}}$ accounts for history-binding failures in the computational analysis. Algorithm 11's terminal comparisons and handoff conditions are deterministic premises; any additional terminal proof system contributes its own soundness term.

**Fiat–Shamir security.** The bounds above give conditional algebraic soundness guarantees under fresh transcript randomness, including field-sampling bias and the stated per-candidate PoW bounds. Let $q$ bound the adversary's total random-oracle queries across all transcript and nonce trials. A complete Fiat–Shamir proof must establish round-by-round soundness for the composed protocol and derive its computational soundness bound as a function of $q$, accounting for adaptive trials, repeated oracle inputs and commitment binding. The main unresolved obligations are WHIR's proximity/list-decoding invariant and the memory participant-binding, event-encoding and execution-reconstruction lemmas. Recursive composition additionally requires the handoff guarantees stated in Algorithm 11.

**References:** [GKR](https://people.cs.georgetown.edu/jthaler/GKRNote.pdf), [LogUp](https://eprint.iacr.org/2022/1530), [GKR lookup compression](https://eprint.iacr.org/2023/1284), [WHIR](https://eprint.iacr.org/2024/1586), [Two Shuffles Make a RAM](https://eprint.iacr.org/2023/1115).

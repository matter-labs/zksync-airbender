# Appendix — Protocol algorithms

Parameter reference: `Sec100`, `av_gkr_compiler` at [`c1a6622`](https://github.com/matter-labs/zksync-airbender/commit/c1a662222cafcd96db4383dce737edb79fa62b09).

```text
FullStatement (1a)
  ├─ VerifyChunks → Chunk → SeededChunk → GKR layers → OutputChecks → WHIR
  ├─ CloseMemory → read/write product equality
  └─ ContinueChain → (application result, program-history digest)
TerminalStatement (1b) → SeededChunk → CloseMemory → (application result, program-history digest)
RecursionChain (10c): prove the base program, then repeatedly prove the matching Verifier's execution of FullStatement.
```

> **Fiat–Shamir challenges**
>
> **Parameters:**
>
> - **BabyBear:** seven-round BLAKE2s with messages absorbed as raw 32-bit words. $E$ is BabyBear's quartic extension, with base modulus $p=2^{31}-2^{27}+1$.
> - **Proth120:** Keccak256 with field elements encoded as canonical 16-byte big-endian values and 32-bit messages, including boundary-state and Merkle-cap digest words, encoded little-endian. $E$ is the prime field with modulus $q=7\cdot2^{120}+1$. Each subsequent absorption of an encoded message $m$ updates the seed as $S\leftarrow\mathrm{Keccak256}(S\mathbin{\|}m)$.
>
> **Proof of work (PoW).** When challenge drawing requires $b$ bits of proof of work, Prover supplies a 64-bit nonce (encoded as eight big-endian bytes for Proth120), which both parties absorb into the transcript immediately before drawing. The first output word, 32 bits for BabyBear or 256 bits for Proth120, is reserved for PoW: Verifier accepts only if it has $b$ leading zero bits, and field challenges are sampled from subsequent drawn words. For Proth120 and only when sampling WHIR queries, the first 32-bit word following the 256-bit PoW digest is additionally discarded. At $b=0$, except for WHIR OOD draws (Algorithm 7, step 3.2) and WHIR sumcheck folding challenges (Algorithm 7, step 3.1.3), the nonce is still absorbed and the PoW word skipped, so every nonce passes.
>
> **Transcript flow across FullStatement.** In base/continuation mode, `FullStatement` first absorbs the final state (register values, PC and timestamps) and all chunks' memory commitments (Merkle tree caps), with circuit-family identifiers and RAM initialization/teardown window identifiers. These identify the circuit types and RAM ranges associated with the commitments. Before absorbing a Merkle-cap sequence, it zero-pads to the next block boundary; successive absorb calls otherwise concatenate without padding. The shared challenges $\mathbf{r}_{\mathrm{mem}}$ are drawn after this precommitment (Algorithms 1a and 2).
>
> Each chunk starts a fresh transcript by absorbing its window identifiers, $\mathbf{r}_{\mathrm{mem}}$, and commitments to its setup, memory and remaining witness, omitting absent witness groups (Algorithm 3a). Chunk transcripts proceed in parallel through GKR and WHIR; in the end, chunks' verified memory products are combined without further challenges.
>
> Prover prepares the memory commitments and computes the shared challenges before emitting the proof. Verifier reconstructs the memory transcript during `VerifyChunks` and authenticates the supplied challenges afterward.
>
> The `TerminalStatement` (Algorithm 1b) variant instead initializes one transcript by absorbing the final state, window identifiers, setup cap and merged memory/witness cap. After the combined memory/lookup PoW, both parties draw $\mathbf{r}_{\mathrm{mem}}$ followed by $\mathbf{r}_{\mathrm{lookup}}$ and continue that same transcript through GKR and WHIR.
>
> **Modular reduction sampling.** For BabyBear, each base-field challenge is a drawn 32-bit word reduced modulo $p$. Each extension-field challenge combines four such samples as coefficients in a fixed basis of $E$.
>
> For Proth120, let $S_0$ be the transcript seed before drawing. For each successive challenge $i\ge1$, compute $S_i=\mathrm{Keccak256}(S_{i-1})$ and reduce the first 128 bits of $S_i$, interpreted as a big-endian integer, modulo $q$. Retain $S_i$ as the seed for the next transcript operation.

---

> **Algorithm 1 — Statement verification**
>
> Algorithms 1a and 1b are alternative statement-verification paths.
>
> **Algorithm 1a — FullStatement**
>
> **Configuration**
>
> Prover and Verifier use common values for the following parameters, fixed throughout the protocol:
>
> - $\mathrm{profile}\in\{\mathrm{unrolled},\mathrm{unified}\}$. Unrolled uses separate instruction-family circuits; unified uses one combined instruction-family circuit (delegation circuits stay separate).
> - $\mathrm{mode}\in\{\mathrm{base},\mathrm{continuation}\}$. Base starts a new program-history chain and is meant for proving application execution; continuation validates and continues an incoming chain and is meant for proving recursive Verifier execution.
> - $\mathrm{commitment\text{-}config}\in\{\mathrm{ordinary},\;\mathrm{merged\text{-}feeder}\ \text{if}\ \mathrm{profile}=\mathrm{unified}\land\mathrm{mode}=\mathrm{continuation}\}$: ordinary uses separate Merkle trees for memory and remaining-witness columns; merged-feeder commits both column groups under one shared Merkle tree, except for delegation circuits. These options further impose restrictions on the WHIR (Algorithm 7) trace dimensions, LDE ratios, query counts, and PoW grinding difficulties selected for instruction circuits by Algorithm 12.
>
> **Protocol**
>
> 1. Prover sends `ProgramSetupCaps`, one program-dependent setup cap per instruction family selected by $\mathrm{profile}$ and $\mathrm{mode}$ (Algorithm 12). Each cap jointly commits to that family's committed setup columns, including any program-independent columns grouped with the program-dependent ones. Prover then sends the final RISC-V register values $x_0..x_{31}$ and timestamp limbs, then PC and timestamp limbs. The claimed final state contains 99 raw 32-bit words:
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
> 3. Run $\mathrm{VerifyChunks}(\mathtt{ProgramSetupCaps},\mathbf r_{\mathrm{mem}},T_{\mathrm{mem}})$ (Algorithm 2), obtaining the read/write products $\mathrm{RS},\mathrm{WS}\in E$ and the completed memory transcript $T_{\mathrm{mem}}$.
> 4. Prover sends the 64-bit memory-PoW nonce. Both parties absorb it into $T_{\mathrm{mem}}$, draw one 32-bit PoW word, then sample the shared challenges from subsequent words. Verifier requires at least 19 leading zero bits in the PoW word and equality between the sampled challenges and the supplied $\mathbf r_{\mathrm{mem}}$.
> 5. Run $\mathrm{CloseMemory}(\mathrm{fin},\mathbf{r}_{\mathrm{mem}},\mathrm{RS},\mathrm{WS})$ (Algorithm 9).
> 6. Return $\mathrm{ContinueChain}(\mathtt{ProgramSetupCaps},\mathrm{fin},\mathrm{mode})$ (Algorithm 10b): the application result $(x_{10},\ldots,x_{17})$ and program-history digest $(h_0,\ldots,h_7)$, each eight 32-bit words. Reject if any check or subalgorithm fails.
>
> **Algorithm 1b — TerminalStatement**
>
> **Configuration:** $\mathrm{chunk\text{-}config}=\mathrm{terminal\text{-}wrapper}$, with parameters from Algorithm 12.
>
> **Protocol**
>
> 1. Select circuit $C$ from Algorithm 12's terminal-wrapper entry. Prover sends $\mathrm{fin}$ in the 99-word format from Algorithm 1a, step 1, followed by two RAM initialization/teardown window identifiers $\mathbf{b}$ as 32-bit values, then setup caps `SetupCaps` and memory caps `MemoryCaps`. The number of caps in each group and the number of hashes per cap are specified in Algorithm 12's terminal-wrapper entry.
> 2. Both parties initialize $T_{\mathrm{mem{+}}}$ with seed $\mathrm{Keccak256}(\mathrm{fin}\mathbin{\|}\mathbf{b}\mathbin{\|}\mathtt{SetupCaps}\mathbin{\|}\mathtt{MemoryCaps})$, encoding the concatenation as little-endian 32-bit words.
> 3. Prover sends the 64-bit memory/lookup-PoW nonce. Both parties absorb it into $T_{\mathrm{mem{+}}}$ and draw one 256-bit PoW word. Verifier requires the number of leading zero bits to meet the combined memory/lookup-PoW threshold specified in Algorithm 12. Both parties then sample $\mathbf{r}_{\mathrm{mem}}=(r_{\mathrm{mem},0},\ldots,r_{\mathrm{mem},5},r_{\mathrm{mem},\eta})\in E^7$, followed by $\mathbf{r}_{\mathrm{lookup}}=(r_{\mathrm{lookup},\alpha},r_{\mathrm{lookup},\beta})\in E^2$, from subsequent drawn words.
> 4. Run $\mathrm{SeededChunk}(C,\mathbf{r}_{\mathrm{mem}},\mathbf{r}_{\mathrm{lookup}},\mathbf{b},(\mathtt{MemoryCaps},\varnothing,\mathtt{SetupCaps}),T_{\mathrm{mem{+}}})$ (Algorithm 3b), obtaining $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$ and $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$, together with the updated $T_{\mathrm{mem{+}}}$.
> 5. Run $\mathrm{CloseMemory}(\mathrm{fin},\mathbf{r}_{\mathrm{mem}},\mathrm{RS}_{\mathrm{chunk}}\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{chunk}}\mathrm{WS}_{\mathrm{IT}})$ (Algorithm 9).
> 6. Return from $\mathrm{fin}$: the application result $(x_{10},\ldots,x_{17})$ and program-history digest $(h_0,\ldots,h_7)=(x_{18},\ldots,x_{25})$, each eight 32-bit words. Reject if any check or subalgorithm fails.

---

> **Algorithm 2 — VerifyChunks**
>
> **Configuration:** Inherit $\mathrm{profile}$, $\mathrm{mode}$ and $\mathrm{commitment\text{-}config}$ from Algorithm 1a.
>
> **Input:** `ProgramSetupCaps` Merkle tree caps, $\mathbf{r}_{\mathrm{mem}}$ challenges, and the running memory transcript $T_{\mathrm{mem}}$ initialized with $\mathrm{fin}$. **Output:** accumulated read/write products $\mathrm{RS},\mathrm{WS}\in E$ and $T_{\mathrm{mem}}$ extended with the participating memory commitments and identifiers.
>
> 1. Verifier initializes $\mathrm{RS}\leftarrow1$, $\mathrm{WS}\leftarrow1$ and forms the ordered circuit list according to $\mathrm{profile}$:
>
>    - **$\mathrm{profile}=\mathrm{unrolled}$:** the instruction circuits selected by Algorithm 12 for $(\mathrm{profile},\mathrm{mode})$, in their listed order; then the standalone IT circuit; then the delegation circuits in Algorithm 12's fixed order.
>    - **$\mathrm{profile}=\mathrm{unified}$:** the unified instruction circuit; then the delegation circuits in Algorithm 12's fixed order.
>
> 2. For each circuit $C$ in this list:
>
>    1. Prover sends the chunk count $n$: the number of proofs for the selected circuit. Each proof covers one chunk, a trace with the fixed number of rows specified for that circuit in Algorithm 12. If the selected circuit is the unified instruction circuit, Prover sends two counts: the total $n$ and the number $n_{IT}$ of final chunks whose initialization/teardown products also contribute to the memory argument (see step 2.3.4).
>    2. Verifier checks the chunk counts:
>
>       - **Standalone IT circuit:** Verifier requires $1\le n \le 8$.
>       - **Unified instruction circuit:** Verifier requires $1\le n_{\mathrm{IT}}\le n$.
>
>    3. For each chunk, in proof order:
>
>       1. Verifier runs $\mathrm{Chunk}(C,\mathbf{r}_{\mathrm{mem}})$† (Algorithm 3a), obtaining the chunk's main read/write products $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$, the additional initialization/teardown products $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$ for unified instruction chunks, memory caps `MemoryCaps`, setup caps `SetupCaps` and window identifiers $\mathbf{b}$.
>
>          † _Chunk calls may run in parallel, each consuming the separate, non-overlapping portion of proof data corresponding to that chunk._
>
>       2. Verifier checks the returned outputs according to $C$:
>
>          - **Unrolled instruction circuit:** require $\mathbf{b}$ to be empty and `SetupCaps` to match the cap for $C$ in `ProgramSetupCaps`.
>          - **Unified instruction circuit:** require two window identifiers in $\mathbf{b}$ and `SetupCaps` to match the cap for $C$ in `ProgramSetupCaps`. For the first $n-n_{\mathrm{IT}}$ chunks, require $\mathbf{b}=(0,0)$. Across the final $n_{\mathrm{IT}}$ chunks, require the window identifiers, in proof order, to form a strictly increasing sequence in $[0,64)$.
>          - **Standalone IT circuit:** require eight window identifiers in $\mathbf{b}$ and require the identifiers, in proof order across chunks, to form a strictly increasing sequence in $[0,64)$. This circuit has no committed setup tables, so `SetupCaps` is empty and requires no comparison.
>          - **Delegation circuit:** require $\mathbf{b}$ to be empty and `SetupCaps` to match the Verifier's hardcoded cap for $C$.
>
>       3. Both parties absorb the following into $T_{\mathrm{mem}}$, using $C$'s 32-bit family label from Algorithm 12:
>
>          - **Unrolled instruction or delegation circuit:** if this is the first chunk for $C$, absorb its family label padded with fifteen zero words. Then absorb this chunk's `MemoryCaps`.
>          - **Standalone IT circuit:** if this is the first chunk for $C$, absorb its family label padded with fifteen zero words. Then absorb this chunk's `MemoryCaps`, followed by its eight window identifiers $\mathbf{b}$ padded with eight zero words.
>          - **Unified instruction circuit:** absorb $C$'s family label and this chunk's two window identifiers $\mathbf{b}$, padded with thirteen zero words. Then absorb this chunk's `MemoryCaps`.
>       4. Update $\mathrm{RS}\leftarrow\mathrm{RS}\cdot\mathrm{RS}_{\mathrm{chunk}}$ and $\mathrm{WS}\leftarrow\mathrm{WS}\cdot\mathrm{WS}_{\mathrm{chunk}}$. For the final $n_{\mathrm{IT}}$ unified instruction chunks, Verifier also updates $\mathrm{RS}\leftarrow\mathrm{RS}\cdot\mathrm{RS}_{\mathrm{IT}}$ and $\mathrm{WS}\leftarrow\mathrm{WS}\cdot\mathrm{WS}_{\mathrm{IT}}$.
> 3. Verifier requires the following memory-term capacity bounds, using the fixed circuit parameters listed before Algorithm 12. The bounds count only one side of the memory argument ($\mathrm{RS}$ or $\mathrm{WS}$):
>
>    - **Instruction cycles $<2^{36}$:** count each unrolled instruction chunk by its trace rows, or each unified instruction chunk as $2^{24}$ cycles.
>    - **Non-IT memory-argument terms $<2^{40}$:** For each instruction chunk, count four terms per cycle (the fixed bound used for all instruction circuits), using the cycle count specified above. For each delegation chunk, count its rows multiplied by its terms per row, using the fixed circuit parameters listed before Algorithm 12. Sum these contributions across all instruction and delegation chunks and require the total to be below $2^{40}$.
>
> 4. Return $\mathrm{RS},\mathrm{WS},T_{\mathrm{mem}}$.

---

> **Algorithm 3 — Chunk preparation and verification**
>
> For standard verification, Algorithm 2 calls Algorithm 3a, which prepares the chunk and invokes Algorithm 3b. Terminal verification uses Algorithm 1b's preparation and then calls Algorithm 3b directly.
>
> **Algorithm 3a — Chunk**
>
> **Configuration:** $\mathrm{chunk\text{-}config}=\mathrm{standard}$; inherit $\mathrm{profile}$, $\mathrm{mode}$ and $\mathrm{commitment\text{-}config}$ from Algorithm 2.
>
> **Input:** compiled arithmetic circuit $C$ and memory challenges $\mathbf{r}_{\mathrm{mem}}$. **Output:** read/write products $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$, the additional initialization/teardown products $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$ for unified instruction chunks, memory caps `MemoryCaps`, setup caps `SetupCaps` and window identifiers $\mathbf{b}$.
>
> 1. Prover sends the RAM initialization/teardown window identifiers $\mathbf{b}$ as 32-bit values according to $C$:
>
>    - **Standalone IT circuit:** eight values.
>    - **Unified instruction circuit:** two values.
>    - **Otherwise:** $\mathbf{b}$ is empty and no values are sent.
>
> 2. Prover sends `SetupCaps`, `MemoryCaps` and `WitnessCaps`, in that order. The number of caps in each group and the number of hashes per cap are specified in Algorithm 12 for $C$ and the inherited $(\mathrm{profile},\mathrm{mode},\mathrm{commitment\text{-}config})$ configuration parameters.
>
> 3. Both parties start a fresh transcript $T_{\mathrm{chunk}}$ by absorbing the ordered prefix below:
>
>    $$
>    \mathbf{b}\mathbin{\|}\mathbf{r}_{\mathrm{mem}}\mathbin{\|}\mathtt{SetupCaps}\mathbin{\|}\mathtt{MemoryCaps}\mathbin{\|}\mathtt{WitnessCaps}
>    $$
>
> 4. Prover sends the 64-bit lookup-PoW nonce. Both parties absorb it into $T_{\mathrm{chunk}}$ and draw one 32-bit PoW word. Verifier requires the number of leading zero bits to meet the lookup-PoW threshold specified in Algorithm 12. Both parties then sample the lookup challenges $\mathbf{r}_{\mathrm{lookup}}=(r_{\mathrm{lookup},\alpha},r_{\mathrm{lookup},\beta})\in E^2$ from subsequent words.
> 5. Run $\mathrm{SeededChunk}(C,\mathbf{r}_{\mathrm{mem}},\mathbf{r}_{\mathrm{lookup}},\mathbf{b},(\mathtt{MemoryCaps},\mathtt{WitnessCaps},\mathtt{SetupCaps}),T_{\mathrm{chunk}})$ (Algorithm 3b), obtaining $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$, the additional pair $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$ when present, and the updated $T_{\mathrm{chunk}}$.
> 6. Return $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$ and $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$, when present, from step 5, together with `MemoryCaps`, `SetupCaps` and $\mathbf{b}$ from steps 1–2.
>
> **Algorithm 3b — SeededChunk**
>
> **Configuration:** $\mathrm{chunk\text{-}config}\in\{\mathrm{standard},\mathrm{terminal\text{-}wrapper}\}$, fixed to $\mathrm{standard}$ by Algorithm 3a and $\mathrm{terminal\text{-}wrapper}$ by Algorithm 1b. For $\mathrm{standard}$, inherit $\mathrm{profile}$, $\mathrm{mode}$ and $\mathrm{commitment\text{-}config}$ from Algorithm 3a.
>
> **Input:** compiled arithmetic circuit $C$, memory challenges $\mathbf{r}_{\mathrm{mem}}$, lookup challenges $\mathbf{r}_{\mathrm{lookup}}$, window identifiers $\mathbf{b}$, cap groups $(\mathtt{MemoryCaps},\mathtt{WitnessCaps},\mathtt{SetupCaps})$ and the prepared transcript $T_{\mathrm{chunk}}$. **Output:** read/write products $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$, the additional initialization/teardown products $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$ for unified instruction chunks, and the updated transcript $T_{\mathrm{chunk}}$.
>
> 1. Both parties run GKR:
>
>    1. Prover sends $s$ claimed output tables $A_0,\ldots,A_{s-1}$ of $C$, each containing sixteen elements of $E$, with $s$ and the table order specified by $C$'s output layout in Algorithm 12. Both parties absorb the tables into $T_{\mathrm{chunk}}$ as one concatenated message in that order, then sample the GKR evaluation point $\mathbf{z}_{\mathrm{gkr}}=(z_{\mathrm{gkr},0},\ldots,z_{\mathrm{gkr},3})\in E^4$ and batching challenge $r_{\mathrm{batch},\mathrm{gkr}}\in E$.
>    2. Initialize $\mathbf{a}_{\mathrm{gkr}}\leftarrow(\mathrm{MLE}(A_0)(\mathbf{z}_{\mathrm{gkr}}),\ldots,\mathrm{MLE}(A_{s-1})(\mathbf{z}_{\mathrm{gkr}}))$, where $\mathrm{MLE}(A)$ is $A$'s multilinear extension.
>    3. Let $2^n$ be $C$'s trace row count from Algorithm 12. Process $C$'s compression layers for $k=4,\ldots,n-1$, followed by its main layers from outputs towards inputs. For each layer $C_{\mathrm{layer}}$, update using Algorithm 4:
>
>       $$
>       ((\mathbf{z}_{\mathrm{gkr}},\mathbf{a}_{\mathrm{gkr}}),r_{\mathrm{batch},\mathrm{gkr}},T_{\mathrm{chunk}})\leftarrow\mathrm{GKRLayer}(C_{\mathrm{layer}},(\mathbf{z}_{\mathrm{gkr}},\mathbf{a}_{\mathrm{gkr}}),r_{\mathrm{batch},\mathrm{gkr}},\mathbf{r}_{\mathrm{mem}},\mathbf{r}_{\mathrm{lookup}},\mathbf{b},T_{\mathrm{chunk}}).
>       $$
>    4. Take the column-packing factor $\mathrm{pack}=2^k$ from Algorithm 12 using $\mathrm{chunk\text{-}config}$.
>
>       - **$k=0$:** set $(\mathbf{z}_{\mathrm{whir}},\mathbf{a}_{\mathrm{whir}})\leftarrow(\mathbf{z}_{\mathrm{gkr}},\mathbf{a}_{\mathrm{gkr}})$.
>       - **$k>0$:** Pad each of the two groups in $\mathbf{a}_{\mathrm{gkr}}$, the merged memory/witness claims and the setup claims as specified in Algorithm 12, with trailing zeros to a multiple of $\mathrm{pack}$ entries, preserving their order. Both parties sample $(z_{\mathrm{gkr},n},\ldots,z_{\mathrm{gkr},n+k-1})\in E^k$ from $T_{\mathrm{chunk}}$. Set:
>
>         $$
>         \begin{aligned}
>         \mathbf{a}_{\mathrm{whir}}&\leftarrow\bigl(\mathrm{MLE}((a_{\mathrm{gkr},0},\ldots,a_{\mathrm{gkr},\mathrm{pack}-1}))(z_{\mathrm{gkr},n},\ldots,z_{\mathrm{gkr},n+k-1}),\\
>         &\qquad\mathrm{MLE}((a_{\mathrm{gkr},\mathrm{pack}},\ldots,a_{\mathrm{gkr},2\mathrm{pack}-1}))(z_{\mathrm{gkr},n},\ldots,z_{\mathrm{gkr},n+k-1}),\ldots\bigr),\\
>         \mathbf{z}_{\mathrm{whir}}&\leftarrow(\mathbf{z}_{\mathrm{gkr}},z_{\mathrm{gkr},n},\ldots,z_{\mathrm{gkr},n+k-1}).
>         \end{aligned}
>         $$
>
> 2. Run $\mathrm{OutputChecks}(C,A_0,\ldots,A_{s-1})$ (Algorithm 6), obtaining the read/write products $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$ and, if $C$ is the unified instruction circuit, the additional initialization/teardown products $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$.
>
> 3. Prover sends the 64-bit batching/proximity-PoW nonce. Both parties absorb it into $T_{\mathrm{chunk}}$ and draw one 32-bit PoW word (256-bit for Proth120 transcript). Verifier requires the number of leading zero bits to meet the batching-PoW threshold specified in Algorithm 12 for $C$ and the selected configuration. Both parties then sample the WHIR batching challenge $r_{\mathrm{batch},\mathrm{whir}}\in E$ from subsequent words.
>
> 4. Set $T_{\mathrm{chunk}}\leftarrow\mathrm{WHIR}(C,(\mathtt{MemoryCaps},\mathtt{WitnessCaps},\mathtt{SetupCaps}),(\mathbf{z}_{\mathrm{whir}},\mathbf{a}_{\mathrm{whir}}),r_{\mathrm{batch},\mathrm{whir}},T_{\mathrm{chunk}})$ (Algorithm 7).
>
> 5. Return $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$, the additional pair $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$ when present, and the updated $T_{\mathrm{chunk}}$.

---

> **Algorithm 4 — GKRLayer**
>
> **Input:** fixed circuit layer $C_{\mathrm{layer}}$, output evaluation point $\mathbf{z}_{\mathrm{gkr}}$ and claims $\mathbf{a}_{\mathrm{gkr}}$, batching challenge $r_{\mathrm{batch},\mathrm{gkr}}$, shared memory challenges $\mathbf{r}_{\mathrm{mem}}$, lookup challenges $\mathbf{r}_{\mathrm{lookup}}$, window identifiers $\mathbf{b}$ and the running chunk transcript $T_{\mathrm{chunk}}$. **Output:** preceding-layer evaluation point $\mathbf{z}'_{\mathrm{gkr}}$, claims $\mathbf{a}'_{\mathrm{gkr}}$, next batching challenge $r'_{\mathrm{batch},\mathrm{gkr}}$, and the updated transcript $T_{\mathrm{chunk}}$.
>
> 1. Both parties batch the incoming claims $\mathbf{a}_{\mathrm{gkr}}$ via RLC using powers of $r_{\mathrm{batch},\mathrm{gkr}}$ in the order specified by $C_{\mathrm{layer}}$, obtaining the initial sumcheck claim $v_{\mathrm{sumcheck}}$.
>
> 2. Run $\mathrm{EQSumcheck}(C_{\mathrm{layer}},(\mathbf{z}_{\mathrm{gkr}},v_{\mathrm{sumcheck}}),T_{\mathrm{chunk}})$ (Algorithm 5) for the layer's batched gate polynomial, obtaining the sumcheck evaluation point $\mathbf{z}_{\mathrm{sumcheck}}$, scalar residual claim $v_{\mathrm{sumcheck}}$, final-coordinate EQ factor $e$ and updated transcript $T_{\mathrm{chunk}}$.
>
> 3. Prover sends $\mathbf{a}_{\mathrm{sumcheck}}$: claimed evaluations of all input polynomials required by $C_{\mathrm{layer}}$ and, for main layers only, cached relation outputs (including claimed virtual-setup polynomial evaluations), in $C_{\mathrm{layer}}$'s prescribed evaluation order.
>
> 4. Verifier evaluates the layer's gates from $\mathbf{a}_{\mathrm{sumcheck}}$:
>
>    - **Compression layer:** Verifier combines the pairwise claimed evaluations at $(0,\mathbf{z}_{\mathrm{sumcheck}})$ and $(1,\mathbf{z}_{\mathrm{sumcheck}})$ using the layer's memory-product or rational-sum LogUp accumulation relations.
>
>    - **Main layer:** Verifier uses the gate-input evaluations at $\mathbf{z}_{\mathrm{sumcheck}}$, including cached relation outputs where applicable, to evaluate copy/linear relations, quadratic arithmetic, memory-product and lookup relations (using $\mathbf{r}_{\mathrm{mem}}$, $\mathbf{r}_{\mathrm{lookup}}$ and $\mathbf{b}$ where required), and zero-constraint expressions as specified by $C_{\mathrm{layer}}$'s gates. Verifier also evaluates the cached relations using claimed inputs from $\mathbf{a}_{\mathrm{sumcheck}}$ where needed and computes virtual lookup-table expressions directly at $\mathbf{z}_{\mathrm{sumcheck}}$. He requires the claimed cached outputs, including virtual setup evaluations, to equal the corresponding computed values.
>
>
>    Verifier batches the resulting scalar gate evaluations using the same powers of $r_{\mathrm{batch},\mathrm{gkr}}$ and the same order as in step 1. He then scales this batch by the final-coordinate EQ factor $e$ returned by Algorithm 5, and requires the result to equal $v_{\mathrm{sumcheck}}$.
>
> 5. Both parties update the transcript and draw challenges according to the layer type:
>
>    - **Compression layer:** Both parties absorb $\mathbf{a}_{\mathrm{sumcheck}}$ into $T_{\mathrm{chunk}}$ and draw $z_{\mathrm{sumcheck},\mathrm{pair}}$ for interpolating the endpoint claims and $r'_{\mathrm{batch},\mathrm{gkr}}$ for batching the next layer's claims.
>
>    - **Main layer:** Both parties absorb $\mathbf{a}_{\mathrm{sumcheck}}$ into $T_{\mathrm{chunk}}$ and draw $r'_{\mathrm{batch},\mathrm{gkr}}$ for batching the next layer's claims.
>
> 6. Both parties prepare the preceding-layer point and claims according to the layer type:
>
>    - **Compression layer:** Both parties set $\mathbf{z}'_{\mathrm{gkr}}\leftarrow(z_{\mathrm{sumcheck},\mathrm{pair}},\mathbf{z}_{\mathrm{sumcheck}})$ and obtain $\mathbf{a}'_{\mathrm{gkr}}$ by evaluating the MLE of each pair in $\mathbf{a}_{\mathrm{sumcheck}}$ at $z_{\mathrm{sumcheck},\mathrm{pair}}$.
>
>    - **Main layer:** Both parties set $\mathbf{z}'_{\mathrm{gkr}}\leftarrow\mathbf{z}_{\mathrm{sumcheck}}$ and obtain $\mathbf{a}'_{\mathrm{gkr}}$ by filtering $\mathbf{a}_{\mathrm{sumcheck}}$ to retain only claimed evaluations of input polynomials, then reordering them according to the next layer's layout or, for the final main layer, the fixed WHIR order: memory, witness, setup, with increasing column index within each group.
>
> 7. Both parties return $(\mathbf{z}'_{\mathrm{gkr}},\mathbf{a}'_{\mathrm{gkr}},r'_{\mathrm{batch},\mathrm{gkr}},T_{\mathrm{chunk}})$.

---

> **Algorithm 5 — EQSumcheck**
>
> **Input:** fixed circuit layer $C_{\mathrm{layer}}$ of degree at most 2, incoming point $\mathbf{z}_{\mathrm{gkr}}$, initial batched claim $v_{\mathrm{sumcheck}}$ and the running chunk transcript $T_{\mathrm{chunk}}$. **Output:** point $\mathbf{z}_{\mathrm{sumcheck}}$, updated scalar residual claim $v_{\mathrm{sumcheck}}$, final-coordinate EQ factor $e$, and the updated transcript $T_{\mathrm{chunk}}$.
>
>> This algorithm reduces the initial weighted sum claim below to a polynomial evaluation claim. Here $m$ is the number of coordinates of $\mathbf{z}_{\mathrm{gkr}}$, $G$ is the batched gate polynomial computed in step 2, and $\mathrm{eq}$ is the Boolean-cube interpolation kernel:
>>
>> $$
>> \begin{aligned}
>> v_{\mathrm{sumcheck}}&=\sum_{\mathbf{x}\in\{0,1\}^m}\mathrm{eq}(\mathbf{z}_{\mathrm{gkr}},\mathbf{x})G(\mathbf{x}),\\
>> \mathrm{eq}(\mathbf{u},\mathbf{x})&=\prod_j((1-u_j)(1-x_j)+u_jx_j).
>> \end{aligned}
>> $$
>>
> 1. Both parties initialize $e\leftarrow1$.
> 2. Prover computes $G\in E^{\le2}[X_0,\ldots,X_{m-1}]$ (degree at most two in each variable) by batching the layer gate expressions from Algorithm 4, step 4, with the same powers of $r_{\mathrm{batch},\mathrm{gkr}}$ and ordering as in Algorithm 4, step 1.
> 3. Both parties run the following rounds for $j=0,\ldots,m-1$:
>    1. Prover computes the univariate round polynomial
>
>       $$
>       g_j(X)=\mathrm{eq}(z_{\mathrm{gkr},j},X)\sum_{\mathbf{x}'\in\{0,1\}^{m-j-1}}\mathrm{eq}(\mathbf{z}_{\mathrm{gkr},>j},\mathbf{x}')G(\mathbf{z}_{\mathrm{sumcheck},<j},X,\mathbf{x}')
>       $$
>
>       and sends its coefficients, with $\deg g_j\le3$.
>    2. Verifier requires $e\,(g_j(0)+g_j(1))=v_{\mathrm{sumcheck}}$.
>    3. Both parties absorb the coefficients of $g_j$ into $T_{\mathrm{chunk}}$, then draw $z_{\mathrm{sumcheck},j}\in E$.
>    4. Both parties update:
>
>       $$
>       \begin{aligned}
>       v_{\mathrm{sumcheck}} &\leftarrow g_j(z_{\mathrm{sumcheck},j}) \\
>       e &\leftarrow \mathrm{eq}(z_{\mathrm{gkr},j},z_{\mathrm{sumcheck},j})
>       \end{aligned}
>       $$
>
> 4. Both parties return $(\mathbf{z}_{\mathrm{sumcheck}},v_{\mathrm{sumcheck}},e,T_{\mathrm{chunk}})$, leaving the residual claim $v_{\mathrm{sumcheck}}=e\,G(\mathbf{z}_{\mathrm{sumcheck}})$ to be checked by the caller algorithm.

---

> **Algorithm 6 — OutputChecks: memory products and LogUp**
>
> **Input:** compiled arithmetic circuit $C$ and its claimed output tables $A_0,\ldots,A_{s-1}\in E^{16}$, received in Algorithm 3b, step 1.1. **Output:** read/write products $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$ and, for unified instruction circuits, the additional initialization/teardown products $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$.
>
> 1. Verifier selects the two main read/write tables $(A_{\mathrm{RS},\mathrm{chunk}},A_{\mathrm{WS},\mathrm{chunk}})$ from $A_0,\ldots,A_{s-1}$ according to $C$'s output layout. For standalone IT circuits, these are the initialization/teardown tables. He computes the product of the entries in each table:
>
>    $$
>    \begin{aligned}
>    \mathrm{RS}_{\mathrm{chunk}} &\leftarrow \prod_{j=0}^{15}A_{\mathrm{RS},\mathrm{chunk}}[j] \\
>    \mathrm{WS}_{\mathrm{chunk}} &\leftarrow \prod_{j=0}^{15}A_{\mathrm{WS},\mathrm{chunk}}[j]
>    \end{aligned}
>    $$
>
>    If $C$ is the unified instruction circuit, Verifier also selects the two additional initialization/teardown tables $(A_{\mathrm{RS},\mathrm{IT}},A_{\mathrm{WS},\mathrm{IT}})$ from $A_0,\ldots,A_{s-1}$ according to $C$'s output layout and computes the product of the entries in each table:
>
>    $$
>    \begin{aligned}
>    \mathrm{RS}_{\mathrm{IT}} &\leftarrow \prod_{j=0}^{15}A_{\mathrm{RS},\mathrm{IT}}[j] \\
>    \mathrm{WS}_{\mathrm{IT}} &\leftarrow \prod_{j=0}^{15}A_{\mathrm{WS},\mathrm{IT}}[j]
>    \end{aligned}
>    $$
>
> 2. For each lookup category present in $C$'s output layout (at most three: 16-bit range, timestamp range and generic), Verifier selects its numerator and denominator tables $(A_N,A_D)$ from $A_0,\ldots,A_{s-1}$ and performs the following checks:
>    1. Verifier initializes $N\leftarrow 0$, $D\leftarrow 1$.
>    2. For $j=0,\ldots,15$, Verifier updates simultaneously:
>
>       $$
>       (N,D)\leftarrow\bigl(N\,A_D[j]+A_N[j]D,\;D\,A_D[j]\bigr)
>       $$
>
>    3. Verifier requires $N=0$ and $D\ne 0$.
> 3. Verifier returns $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$ and, if $C$ is the unified instruction circuit, $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$.

---

> **Algorithm 7 — WHIR**
>
> **Configuration:** inherit $\mathrm{chunk\text{-}config}$ and, for standard chunks, $\mathrm{commitment\text{-}config}$ from Algorithm 3b.
>
> **Input:** compiled arithmetic circuit $C$, cap groups $(\mathtt{MemoryCaps},\mathtt{WitnessCaps},\mathtt{SetupCaps})$, opening point $\mathbf{z}_{\mathrm{whir}}$ and claims $\mathbf{a}_{\mathrm{whir}}$, batching challenge $r_{\mathrm{batch},\mathrm{whir}}$ and the running chunk transcript $T_{\mathrm{chunk}}$. **Output:** the updated transcript $T_{\mathrm{chunk}}$.
>
>> The running claim is
>>
>> $$
>> v_{\mathrm{whir}}=\sum_{\mathbf{x}}F(\mathbf{x})W(\mathbf{x}).
>> $$
>>
>> Here $F$ is Prover's current multilinear polynomial, initially computed in step 2 and subsequently folded in step 3.1. The polynomial $W$ accumulates the EQ weights of the claims. The sum ranges over the Boolean cube on their remaining variables.
>
> 1. Both parties batch $\mathbf{a}_{\mathrm{whir}}$ via RLC using powers of $r_{\mathrm{batch},\mathrm{whir}}$ in the order inherited from Algorithm 3b, obtaining $v_{\mathrm{whir}}$, and initialize $W(\mathbf{x})\leftarrow\mathrm{eq}(\mathbf{z}_{\mathrm{whir}},\mathbf{x})$ using the EQ kernel from Algorithm 5.
>
> 2. Prover computes $F\in E^{\le1}[X_0,\ldots,X_{m-1}]$, where $m$ is the number of coordinates of $\mathbf{z}_{\mathrm{whir}}$, by batching the committed polynomials corresponding to $\mathbf{a}_{\mathrm{whir}}$ via RLC with the same powers of $r_{\mathrm{batch},\mathrm{whir}}$ and order as in step 1.
>
> 3. Both parties process each round $r$ of the WHIR schedule selected by Algorithm 12 for $C$, $\mathrm{chunk\text{-}config}$ and $\mathrm{commitment\text{-}config}$, with $m_r=m-\sum_{i<r}k_i$ variables at the start of round $r$:
>    1. Both parties run $k_r$ sumcheck rounds, indexed by $j=0,\ldots,k_r-1$, where $k_r$ is the fold count selected by Algorithm 12 for WHIR round $r$. Denote their challenges by $\mathbf{z}_{\mathrm{fold},r}=(z_{\mathrm{fold},r,0},\ldots,z_{\mathrm{fold},r,k_r-1})$:
>       1. Prover computes the univariate round polynomial
>
>          $$
>          g_j(X)=\sum_{\mathbf{x}\in\{0,1\}^{m_r-j-1}}F(X,\mathbf{x})W(X,\mathbf{x})
>          $$
>
>          and sends its three coefficients, with $\deg g_j\le2$.
>       2. Verifier requires $g_j(0)+g_j(1)=v_{\mathrm{whir}}$.
>       3. Both parties absorb the coefficients into $T_{\mathrm{chunk}}$ and draw $z_{\mathrm{fold},r,j}\in E$.
>       4. Prover sets $F\leftarrow F(z_{\mathrm{fold},r,j},\cdot)$; both parties set $W\leftarrow W(z_{\mathrm{fold},r,j},\cdot)$ and $v_{\mathrm{whir}}\leftarrow g_j(z_{\mathrm{fold},r,j})$.
>    2. Prover supplies the folded polynomial according to the round, writing $\mathrm{powers}(x)=(x,x^2,\ldots,x^{2^{m_r-k_r-1}})$ for the $m_r-k_r$ remaining variables:
>
>       - **Intermediate round:**
>
>         1. Prover sends `WhirCap_r`, committing to $F$ on the next domain from Algorithm 12. Both parties absorb `WhirCap_r` into $T_{\mathrm{chunk}}$.
>         2. Both parties draw $z_{\mathrm{ood},r}\in E$. Prover sends $a_{\mathrm{ood},r}$, claiming $a_{\mathrm{ood},r}=F(\mathbf{z}_{\mathrm{ood},r})$, where $\mathbf{z}_{\mathrm{ood},r}=\mathrm{powers}(z_{\mathrm{ood},r})$. Both parties absorb $a_{\mathrm{ood},r}$ into $T_{\mathrm{chunk}}$.
>
>       - **Final round:** Prover sends the $2^{m_r-k_r}$ coefficients $\mathbf{c}=(c_0,\ldots,c_{2^{m_r-k_r}-1})$ of the univariate polynomial $f(x)=F(\mathrm{powers}(x))$, in increasing degree order. Both parties absorb $\mathbf{c}$ into $T_{\mathrm{chunk}}$.
>
>    3. Prover sends the 64-bit query-PoW nonce. Both parties absorb it into $T_{\mathrm{chunk}}$ and draw one 32-bit PoW word (256-bit for Proth120). Verifier requires the number of leading zero bits to meet the query-PoW threshold specified in Algorithm 12 for round $r$. Both parties sample $t_r$ folding-coset indices $I_{r,j}\in\{0,\ldots,|D_r|/2^{k_r}-1\}$ from subsequently drawn transcript bits, where $t_r$ is the round's query count and $D_r$ its pre-folding domain, both specified by Algorithm 12, and set $z_{\mathrm{query},r,j}\leftarrow(\omega^{I_{r,j}})^{2^{k_r}}$ and $\mathbf{z}_{\mathrm{query},r,j}\leftarrow\mathrm{powers}(z_{\mathrm{query},r,j})$ for each query, where $\omega$ generates $D_r$.
>
>       If this is not the last round, both parties discard any unused bits in the current 256-bit transcript output block, then draw $r_{\mathrm{batch},\mathrm{evals},r}\in E$ from fresh transcript output to batch the OOD and query evaluation claims.
>    4. For each query $j=0,\ldots,t_r-1$:
>       1. Prover sends leaves and Merkle authentication paths for the trees belonging to `MemoryCaps`, `WitnessCaps` and `SetupCaps` in the first round (evaluation leaves for all base polynomials at the $2^{k_r}$-th roots of $z_{\mathrm{query},r,j}$), and to `WhirCap_{r-1}` in later rounds (coefficient leaves for the single batched polynomial at the same roots).
>       2. Verifier authenticates each leaf against its cap at the tree position specified by Algorithm 12 and folds each polynomial's leaf values using $\mathbf{z}_{\mathrm{fold},r}$ to compute its evaluation at $\mathbf{z}_{\mathrm{query},r,j}$ (evaluation in the remaining variables is already incorporated in the leaf values), according to the leaf encoding:
>
>          - **Coefficient leaves:** For $i=0,\ldots,k_r-1$, Verifier replaces each adjacent pair $c_0,c_1$ of the current values, starting from each polynomial's authenticated coefficients in leaf order, by
>
>            $$
>            \operatorname{Int}[(0,A),(1,B)](z_{\mathrm{fold},r,i})
>            =A+z_{\mathrm{fold},r,i}(B-A)
>            =c_0+z_{\mathrm{fold},r,i}c_1,
>            $$
>
>            where $A$ and $B$ are the corresponding evaluations at $0,1$, and $\operatorname{Int}$ denotes linear interpolation through the specified points.
>
>          - **Evaluation leaves:** For $i=0,\ldots,k_r-1$, Verifier pairs the current values $A,B$ at nonzero coset points $x,-x$ in the configured coset order and replaces each pair by
>
>            $$
>            \frac{A+B+z_{\mathrm{fold},r,i}(A-B)/x}{2}.
>            $$
>
>            Between folding steps, Verifier updates each point $x\leftarrow x^2$.
>
>       3. Verifier sets $a_{\mathrm{query},r,j}$ as follows:
>
>          - **First round:** batch the per-polynomial folded evaluations from step 3.4.2 using the same powers of $r_{\mathrm{batch},\mathrm{whir}}$ and order as in step 1.
>          - **Later rounds:** use the single folded evaluation from step 3.4.2.
>    5. Both parties finish the round according to its type:
>
>       - **Intermediate round:** Both parties update
>
>         $$
>         \begin{aligned}
>         W(\mathbf{x}) &\leftarrow W(\mathbf{x})+r_{\mathrm{batch},\mathrm{evals},r}\,\mathrm{eq}(\mathbf{z}_{\mathrm{ood},r},\mathbf{x})
>           +\sum_{j=0}^{t_r-1}r_{\mathrm{batch},\mathrm{evals},r}^{j+2}\mathrm{eq}(\mathbf{z}_{\mathrm{query},r,j},\mathbf{x}),\\
>         v_{\mathrm{whir}} &\leftarrow v_{\mathrm{whir}}+r_{\mathrm{batch},\mathrm{evals},r} a_{\mathrm{ood},r}+\sum_{j=0}^{t_r-1}r_{\mathrm{batch},\mathrm{evals},r}^{j+2}a_{\mathrm{query},r,j}.
>         \end{aligned}
>         $$
>
>       - **Final round:** Verifier requires $a_{\mathrm{query},r,j}=f(z_{\mathrm{query},r,j})$ for every query. He interprets $\mathbf{c}$ as the monomial coefficients of $F_{\mathrm{final}}$ using the encoding in step 3.2 and requires
>
>         $$
>         v_{\mathrm{whir}}=\sum_{\mathbf{x}\in\{0,1\}^{m_r-k_r}}F_{\mathrm{final}}(\mathbf{x})W(\mathbf{x}).
>         $$
>
> 4. Both parties return $T_{\mathrm{chunk}}$.

---

> **Algorithm 9 — CloseMemory**
>
> **Input:** final state $\mathrm{fin}$, shared challenges $\mathbf{r}_{\mathrm{mem}}=(r_{\mathrm{mem},0},\ldots,r_{\mathrm{mem},5},r_{\mathrm{mem},\eta})$, authenticated products $\mathrm{RS},\mathrm{WS}$.
>
> 1. Verifier forms the multiset `Initial` with one write event per register $i=0,\ldots,31$, with value 0 at timestamp 0, and one PC write event with value 0 at timestamp 4.
> 2. Verifier forms the multiset `Final` with one read event per register $i=0,\ldots,31$, using value $x_i$ and timestamp limbs $(\mathrm{ts}_{i,\mathrm{lo}},\mathrm{ts}_{i,\mathrm{hi}})$ from $\mathrm{fin}$, and one PC read event using $\mathrm{pc}$ and $(\mathrm{ts}_{\mathrm{pc},\mathrm{lo}},\mathrm{ts}_{\mathrm{pc},\mathrm{hi}})$ from $\mathrm{fin}$.
> 3. Verifier represents each event in `Initial` and `Final` as $\mathbf{t}=(\mathrm{tag},\mathrm{addr}_{\mathrm{lo}},\mathrm{addr}_{\mathrm{hi}},\mathrm{ts}_{\mathrm{lo}},\mathrm{ts}_{\mathrm{hi}},\mathrm{val}_{\mathrm{lo}},\mathrm{val}_{\mathrm{hi}})$, with $\mathrm{tag}$ equal to 0 for registers, 1 for RAM and 2 for the PC. The address is $i$ for register $i$ and 0 for the PC cell. Address and value pairs use 16-bit limbs and encode $\mathrm{lo}+2^{16}\mathrm{hi}$; timestamp pairs use 19-bit limbs and encode $\mathrm{lo}+2^{19}\mathrm{hi}$, taking the final timestamp limbs as sent in $\mathrm{fin}$.
>
>    Verifier encodes each event as
>
>    $$
>    \begin{aligned}
>    L_{\mathbf{r}_{\mathrm{mem}}}(\mathbf{t})
>      &=\mathrm{tag}+r_{\mathrm{mem},\eta} \\
>      &\quad+r_{\mathrm{mem},0}\,\mathrm{addr}_{\mathrm{lo}}+r_{\mathrm{mem},1}\,\mathrm{addr}_{\mathrm{hi}} \\
>      &\quad+r_{\mathrm{mem},2}\,\mathrm{ts}_{\mathrm{lo}}+r_{\mathrm{mem},3}\,\mathrm{ts}_{\mathrm{hi}} \\
>      &\quad+r_{\mathrm{mem},4}\,\mathrm{val}_{\mathrm{lo}}+r_{\mathrm{mem},5}\,\mathrm{val}_{\mathrm{hi}}
>    \end{aligned}
>    $$
>
>    Verifier multiplies $\mathrm{WS}$ by the encoded `Initial` events and $\mathrm{RS}$ by the encoded `Final` events:
>
>    $$
>    \begin{aligned}
>    \mathrm{WS} &\leftarrow \mathrm{WS}\prod_{\mathbf{t}\in\mathrm{Initial}}L_{\mathbf{r}_{\mathrm{mem}}}(\mathbf{t}) \\
>    \mathrm{RS} &\leftarrow \mathrm{RS}\prod_{\mathbf{t}\in\mathrm{Final}}L_{\mathbf{r}_{\mathrm{mem}}}(\mathbf{t})
>    \end{aligned}
>    $$
>
>    RAM initialization and teardown products are already included in $\mathrm{RS}$ and $\mathrm{WS}$.
>
> 4. Verifier requires $\mathrm{RS}=\mathrm{WS}$.

---

> **Algorithm 10a — EndParameters**
>
> **Input:** program setups `ProgramSetupCaps` and ending PC $\mathrm{pc}$. **Output:** end program parameters $e$, eight 32-bit words, identifying the program together with its ending PC.
>
> **Notation:** `Hash` uses seven-round BLAKE2s with messages absorbed as raw 32-bit words.
>
> 1. Return:
>
>    $$
>    e\leftarrow\mathrm{Hash}\bigl((\mathrm{pc},0^{15})\mathbin{\|}\mathtt{ProgramSetupCaps}\bigr)
>    $$
>
>    After PC, `Hash` zero-pads to fill the current input block (15 words), then absorbs the ordered setup caps. No other part of the final state enters $e$; in particular, register values and timestamps are excluded.
>
> **Algorithm 10b — ContinueChain**
>
> **Input:** program setups `ProgramSetupCaps`, final state $\mathrm{fin}$ and base/continuation $\mathrm{mode}$. **Output:** application result $\mathbf{y}$ and program-history digest $h$, each eight 32-bit words.
>
> **Notation:** $x_j$ and $\mathrm{pc}$ come from $\mathrm{fin}$; `Hash` is as in Algorithm 10a.
>
> 1. Set $\mathbf{y}\leftarrow(x_{10},\ldots,x_{17})$ and $e\leftarrow\mathrm{EndParameters}(\mathtt{ProgramSetupCaps},\mathrm{pc})$ (Algorithm 10a).
> 2. **Base mode:** require $(x_{18},\ldots,x_{25})=0^8$; set $h\leftarrow\mathrm{Hash}(0^8\mathbin{\|}e)$.
> 3. **Otherwise, continuation mode:**
>    1. Set $h_{\mathrm{in}}\leftarrow(x_{18},\ldots,x_{25})$.
>    2. Prover sends the 16-word hash-chain preimage $(h_{\mathrm{prev}},e_{\mathrm{prev}})$, eight 32-bit words each. Verifier requires $\mathrm{Hash}(h_{\mathrm{prev}}\mathbin{\|}e_{\mathrm{prev}})=h_{\mathrm{in}}$.
>    3. **If $e_{\mathrm{prev}}=e$:** set $h\leftarrow h_{\mathrm{in}}$.
>    4. **Otherwise:** set $h\leftarrow\mathrm{Hash}(h_{\mathrm{in}}\mathbin{\|}e)$.
> 4. Return $(\mathbf{y},h)$.
>
> **Algorithm 10c — RecursionChain**
>
> **Public input:** base program binary $B$, together with the pre-agreed circuit definitions and their parameters (Algorithm 12). **Witness:** the non-determinism responses $\omega$ consumed by the execution of $B$. This is the only free Prover input: every later program in the chain is a fixed Verifier program, and its non-determinism responses are the previous proof. **Output:** the final proof after $T\ge0$ recursive steps. Its final state carries the application result $\mathbf{y}$ and the program history of all preceding proofs.
>
> **Notation:**
>
> - $\mathrm{cfg}=(\mathrm{profile},\mathrm{mode},\mathrm{commitment\text{-}config})$ is a configuration of Algorithm 1a.
> - $\mathrm{Prove}_{\mathrm{cfg}}(\Pi,\nu)$ executes the RISC-V program $\Pi$ with non-determinism responses $\nu$ and outputs a proof bundle for `FullStatement` under $\mathrm{cfg}$: the `ProgramSetupCaps` of $\Pi$, the final state $\mathrm{fin}$, the chunk proofs and, in continuation mode, the hash-chain preimage of Algorithm 10b, step 3.2.
> - $\mathrm{stream}(P)$ is the `ProgramSetupCaps` of proof bundle $P$ followed by its remaining messages, serialized in the order `FullStatement` reads them.
> - $V[\mathrm{cfg}]$ is the Verifier program matching $\mathrm{cfg}$. It reads $\mathrm{stream}(P)$ as its non-determinism responses and runs `FullStatement` under $\mathrm{cfg}$. It reaches its successful ending PC only if `FullStatement` accepts, with the returned $\mathbf{y}$ in $x_{10},\ldots,x_{17}$ and $h$ in $x_{18},\ldots,x_{25}$. The chain uses $V^{\mathrm{unr}}_{\mathrm{base}}=V[(\mathrm{unrolled},\mathrm{base},\mathrm{ordinary})]$, $V^{\mathrm{unr}}_{\mathrm{cont}}=V[(\mathrm{unrolled},\mathrm{continuation},\mathrm{ordinary})]$, $V^{\mathrm{uni}}_{\mathrm{cont}}=V[(\mathrm{unified},\mathrm{continuation},\mathrm{ordinary})]$ and, on the L1 route, the build of $V^{\mathrm{uni}}_{\mathrm{cont}}$ that computes BLAKE2s directly with RISC-V instructions, and the feeder Verifier $V[(\mathrm{unified},\mathrm{continuation},\mathrm{merged\text{-}feeder})]$, which computes BLAKE2s the same way.
> - $\mathrm{pc}_{\mathrm{ok}}(\Pi)$ is the successful ending PC of $\Pi$, and $\mathtt{ProgramSetupCaps}(\Pi,\mathrm{cfg})$ are the setup caps of $\Pi$ for the instruction families selected by $\mathrm{cfg}$ (Algorithm 12). The end program parameters of a successful execution of $\Pi$ proved under $\mathrm{cfg}$ are given by Algorithm 10a:
>
>    $$
>    e(\Pi,\mathrm{cfg})=\mathrm{EndParameters}\bigl(\mathtt{ProgramSetupCaps}(\Pi,\mathrm{cfg}),\mathrm{pc}_{\mathrm{ok}}(\Pi)\bigr)
>    $$
>
> **Protocol**
>
> 1. **Base layer.** Prover executes $B$ on $\omega$ and computes $P_0\leftarrow\mathrm{Prove}_{\mathrm{cfg}_0}(B,\omega)$ with $\mathrm{cfg}_0=(\mathrm{unrolled},\mathrm{base},\mathrm{ordinary})$. This chain construction starts only with the unrolled profile. The execution must end at $\mathrm{pc}_{\mathrm{ok}}(B)$ with $\mathbf{y}$ in $x_{10},\ldots,x_{17}$ and zeros in $x_{18},\ldots,x_{25}$.
> 2. **Recursive steps.** For $t=1,\ldots,T$:
>    1. **Matching Verifier:** set $V_t\leftarrow V[\mathrm{cfg}_{t-1}]$, so $V_1=V^{\mathrm{unr}}_{\mathrm{base}}$ and every later $V_t$ is a continuation Verifier for the profile of $P_{t-1}$.
>    2. **Proving configuration:** choose $\mathrm{cfg}_t=(p_t,\mathrm{continuation},c_t)$ with $p_t\in\{\mathrm{unrolled},\mathrm{unified}\}$. The switch from unrolled to unified is one-way: if $p_{t-1}=\mathrm{unified}$ then $p_t=\mathrm{unified}$. For BabyBear output, $c_t=\mathrm{ordinary}$. On the L1 route, $c_t$ may switch once from $\mathrm{ordinary}$ to $\mathrm{merged\text{-}feeder}$, only with $p_t=\mathrm{unified}$, and remains $\mathrm{merged\text{-}feeder}$ thereafter. At this switch, require $p_{t-1}=\mathrm{unified}$ and set $V_t$ to the L1 build of $V^{\mathrm{uni}}_{\mathrm{cont}}$ defined above.
>    3. **Prove the Verifier's execution:** compute $P_t\leftarrow\mathrm{Prove}_{\mathrm{cfg}_t}(V_t,\mathrm{stream}(P_{t-1}))$. The proved execution runs `FullStatement` on $P_{t-1}$ under $\mathrm{cfg}_{t-1}$, including `ContinueChain` (Algorithm 10b), which computes $e_{t-1}$ and returns $(\mathbf{y},h_{t-1})$. It ends at $\mathrm{pc}_{\mathrm{ok}}(V_t)$ with $\mathbf{y}$ in $x_{10},\ldots,x_{17}$ and $h_{t-1}$ in $x_{18},\ldots,x_{25}$. Prover attaches to $P_t$ the hash-chain preimage of $h_{t-1}$.
> 3. **Output:**
>    - **BabyBear:** output $P_T$.
>    - **L1 wrapping:** require $T\ge1$, $p_T=\mathrm{unified}$ and $c_T=\mathrm{merged\text{-}feeder}$. Prove the execution of the feeder Verifier $V[\mathrm{cfg}_T]$ on $\mathrm{stream}(P_T)$ with the fixed terminal-wrapper parameters (Algorithm 12), and output the resulting proof for `TerminalStatement` (Algorithm 1b).
>
> The identities and history digests along the chain follow Algorithms 10a and 10b:
>
> $$
> e_0=e(B,\mathrm{cfg}_0),\qquad e_t=e(V_t,\mathrm{cfg}_t),\qquad h_0=\mathrm{Hash}(0^8\mathbin{\|}e_0),\qquad h_t=
> \begin{cases}
> h_{t-1}, & e_t=e_{t-1},\\
> \mathrm{Hash}(h_{t-1}\mathbin{\|}e_t), & \text{otherwise.}
> \end{cases}
> $$
>
> The output proof carries $\mathbf{y}$ in $x_{10},\ldots,x_{17}$ and, in $x_{18},\ldots,x_{25}$, the history digest of all proofs before it: $0^8$ for $P_0$, $h_{T-1}$ for $P_T$ with $T\ge1$, and $h_T$ for the L1 wrapper. The output proof's own program is identified by its setup caps and final PC rather than by the registers. Algorithm 11 checks both.
>
> **Static identities.** No identity in the chain depends on $\omega$, and only $e_0$ depends on $B$:
>
> - **Base program:** $\mathtt{ProgramSetupCaps}(B,\mathrm{cfg}_0)$ and $\mathrm{pc}_{\mathrm{ok}}(B)$ are computed from the binary $B$ and the circuit definitions alone, so $e_0$ is known before any execution.
> - **Verifier programs:** each Verifier build is a fixed binary determined by the pre-agreed circuit definitions, proof parameters and BLAKE2s implementation. It receives the child's setup caps through $\mathrm{stream}(P)$ instead of embedding them, so the same binaries verify the chain of any base program. Their identities therefore depend on neither $B$ nor $\omega$ and are precomputed once.
> - **Non-determinism of recursive steps:** $\mathrm{stream}(P_{t-1})$ is computed by Prover from the previous proof. It is not part of the witness of the application claim.
>
> **Admissible histories.** For ordinary commitments write $e^{p}(V)=e(V,(p,\mathrm{continuation},\mathrm{ordinary}))$. For every ordinary-commitment prefix allowed by step 2.2, collapsing consecutive repetitions of its Verifier identities gives a prefix of one of the following sequences, selected by the first step proved with unified circuits:
>
> | First unified step | Collapsed Verifier identities |
> |---|---|
> | $t=1$ | $e^{\mathrm{uni}}(V^{\mathrm{unr}}_{\mathrm{base}}),\ e^{\mathrm{uni}}(V^{\mathrm{uni}}_{\mathrm{cont}})$ |
> | $t=2$ | $e^{\mathrm{unr}}(V^{\mathrm{unr}}_{\mathrm{base}}),\ e^{\mathrm{uni}}(V^{\mathrm{unr}}_{\mathrm{cont}}),\ e^{\mathrm{uni}}(V^{\mathrm{uni}}_{\mathrm{cont}})$ |
> | $t\ge3$, or never | $e^{\mathrm{unr}}(V^{\mathrm{unr}}_{\mathrm{base}}),\ e^{\mathrm{unr}}(V^{\mathrm{unr}}_{\mathrm{cont}}),\ e^{\mathrm{uni}}(V^{\mathrm{unr}}_{\mathrm{cont}}),\ e^{\mathrm{uni}}(V^{\mathrm{uni}}_{\mathrm{cont}})$ |
>
> A history digest is obtained by folding $e_0$ followed by such a prefix through the recurrence above. On the L1 route, extend this history through each merged-feeder step using the recurrence above and the merged-feeder setup caps. The finite list $h_{\mathrm{paths}}$ of Algorithm 11 pairs $(0^8,e_0)$ for the base proof and $(h_{T-1},e_T)$ for later BabyBear proofs; for L1, it pairs $h_T$ with the expected terminal-wrapper `SetupCaps` and successful ending PC. Because repetitions collapse, the list is finite for unbounded $T$ and a digest does not record the number of recursive steps.
>
> **Scheduling.** $T$ and the profiles $p_t$ are Prover's choices and are not part of the proved relation beyond the admissible histories above. The reference pipeline proves with unrolled circuits while the estimated execution length of the next Verifier exceeds a switch threshold, then proves with unified circuits until the proof shape stops shrinking.

---

> **Algorithm 11 — Terminal acceptance of recursion**
>
> **Public claim:** base program binary $B$ and the fixed Verifier programs of Algorithm 10c, unrolled and unified. **Derived:** the preprocessed list $h_{\mathrm{paths}}$ of admissible collapsed histories from Algorithm 10c. Each entry pairs a history digest with the expected identity of the last proof: its end program parameters $e$ (Algorithm 10a) or, for the L1 wrapper, the fixed terminal-wrapper `SetupCaps` and successful ending PC. The history digest is the one carried in the last proof's final-state registers, as specified in Algorithm 10c. **Witness:** the last proof of the chain: a proof bundle for $B$, a proof bundle for a Verifier program proved with unrolled or unified circuits, or the L1 wrapper proof. **Recursive relation:** Prover proved the execution of $B$ under the agreed circuits and then, zero or more times, proved the matching Verifier program's `FullStatement` execution over the previous proof (Algorithm 10c). The last proved execution reaches its successful return with public output $\mathbf{y}$ in $x_{10},\ldots,x_{17}$.
>
> **Terminal acceptance:**
>
> 1. Verify the last proof, retaining the authenticated final state $\mathrm{fin}$ read during verification:
>    - **BabyBear:** run `FullStatement` (Algorithm 1a) under the last proof's configuration.
>    - **L1 wrapping:** run `TerminalStatement` (Algorithm 1b). Require the proof's window identifiers to match those fixed for the terminal Verifier.
> 2. Identify the last proof's program against some entry of $h_{\mathrm{paths}}$:
>    - **BabyBear:** compute $e\leftarrow\mathrm{EndParameters}(\mathtt{ProgramSetupCaps},\mathrm{pc})$ (Algorithm 10a) from the last proof's setup caps and the PC in $\mathrm{fin}$. Require $e$ to equal the entry's expected end program parameters.
>    - **L1 wrapping:** require the last proof's `SetupCaps` and the PC in $\mathrm{fin}$ to match the entry's expected setup caps and successful ending PC.
> 3. Require the history digest $h=(x_{18},\ldots,x_{25})$ in $\mathrm{fin}$ to equal the history digest of the same entry.
> 4. Accept and expose $\mathbf{y}=(x_{10},\ldots,x_{17})$ only if all verification and expectation checks pass; otherwise reject.
>
> The expected identities and $h_{\mathrm{paths}}$ are determined by the base program $B$, the precompiled Verifier programs and the acceptable recursive configurations. The Verifier programs depend only on the circuits' constraints and setups, not on $B$, and nothing in the list depends on the witness of $B$'s execution.
>
> For L1, the EVM Verifier checks the expected final PC and window identifiers. It reports $\mathbf{y}$ and $h$ as little-endian 32-bit register words concatenated in register order, and the setup identity as Keccak256 of the ordered setup-cap digests, with each digest's 32-bit words encoded big-endian. The application or registry performs the expected setup-identity and history comparisons in steps 2–3 using these reported values.

---

**Circuit and memory parameters for base/continuation FullStatement.** Merkle caps contain sixteen 256-bit hashes. $\mathrm{profile}$ and $\mathrm{mode}$ fix the instruction-family selection in Algorithm 12; the families have the following row counts and capacity charges.

- **Unrolled instructions:** add/sub/LUI/AUIPC/MOP (family 1); jump/branch/compare (2); shift/binary (3); unsigned multiply/divide (4); word memory (16); subword memory (17). Trace logarithms are 24 except multiply/divide, which uses 23.
- **Delegations:** BLAKE2s, bigint, Keccak special5, theta/rho, column parity and chi5, with trace logarithms $(20,22,22,22,22,22)$ and memory/permutation-argument terms per chunk $(A_d)_d=(44\cdot2^{20},20\cdot2^{22},15\cdot2^{22},17\cdot2^{22},15\cdot2^{22},13\cdot2^{22})$ in that order.
- **IT windows:** standalone IT has $2^{24}$ rows and eight windows of $2^{24}$ 32-bit words per proof. Unified has two windows of $2^{25}$ bytes per chunk. With identifiers below 64, unified covers windows below $2^{31}$ bytes; unrolled covers the $2^{32}$-byte range.
- **Unified capacity:** each circuit has $2^{23}$ rows but is charged $2^{24}$ cycles by Algorithm 2's cycle-count check.

> **Algorithm 12 — SelectParameters**
>
> **Input:** fixed circuit description $C$, $\mathrm{chunk\text{-}config}\in\{\mathrm{standard},\mathrm{terminal\text{-}wrapper}\}$ and, for $\mathrm{standard}$, $\mathrm{profile}$, $\mathrm{mode}$ and $\mathrm{commitment\text{-}config}$. **Output:** ordered instruction-family list where applicable, field and transcript, commitment layout, column-packing factor $\mathrm{pack}$ and GKR/WHIR parameters. Algorithms 1a and 2 supply $\mathrm{standard}$; Algorithm 1b supplies $\mathrm{terminal\text{-}wrapper}$; Algorithms 3a and 3b supply their selected configuration. All layout choices and proof parameters below are fixed before proof messages are read.
>
> **Packing.** The column-packing factor $\mathrm{pack}$ is $2^{\mathtt{pack\_log2}}$ in the prover configuration. Each packed polynomial represents $\mathrm{pack}$ consecutive columns within one commitment set in its fixed column order. An incomplete final group is completed with identically zero columns; their evaluation claims are therefore zero at every point. Merged memory/witness columns form one set; groups do not cross commitment-set boundaries. Claim groups use the same ordering and zero padding. Coordinate $z_{\mathrm{gkr},n+i}$ binds bit $i$ of the column index within the group, least-significant bit first; these coordinates are appended as the high variables after the trace coordinates.
>
> A set of $c$ columns has $\lceil c/\mathrm{pack}\rceil$ committed polynomials, each with $N=n+\log_2(\mathrm{pack})$ variables. GKR and lookup calculations use $n$; WHIR domain, fold and final-size calculations use $N$. Merged memory/witness columns contribute $\lceil(c_M+c_W)/\mathrm{pack}\rceil$ polynomials.
>
> **Fixed circuit data.** $C$ is the compiled circuit artifact selected below at the reference revision. The artifact contains the circuit's layer relations, arithmetic constraints, lookup specifications, column layouts and output map:
>
> | Data used by the algorithms | Artifact fields |
> |---|---|
> | Trace row count $2^n$ | `trace_len` |
> | Main layers, their gates and auxiliary relations; main-layer count $L_{\mathrm{main}}$ | `layers`; $L_{\mathrm{main}}$ is its length |
> | Output-table count $s$ and order | `global_output_map`; $s$ is the total number of output addresses |
> | Memory and witness column layouts | `memory_layout`, `witness_layout` |
> | Arithmetic constraints and lookup specifications | `degree_1_constraints`, `degree_2_constraints`, `structured_statements`, `generic_lookups`, `range_check_16_lookup_expressions`, `timestamp_range_check_lookup_expressions` |
>
> Output tables follow `global_output_map` in `OutputType` order: `PermutationProduct`, `Lookup16Bits`, `LookupTimestamps`, `GenericLookup`, `InitsAndTeardownsProduct`, omitting absent categories and preserving the address order within each category.
>
> For the sixteen-entry output tables used here, Algorithm 3b makes $n-4$ compression-layer calls and $L_{\mathrm{main}}$ main-layer calls to Algorithm 4, for $L_{\mathrm{main}}+n-4$ GKR layers in total. The main layers are stored in `layers`; the compression layers are derived from the output map and the output dimension $4$, fixed by `sumcheck_explicit_output_size_log_2` in the selected prover configuration.
>
> **Circuit artifacts and GKR dimensions:**
>
> | Circuit (compiled artifact) | Family ID | $n$ | Main layers $L_{\mathrm{main}}$ | Compression layers $n-4$ | Total GKR layers | Output tables $s$ |
> |---|---|---|---|---|---|---|
> | [add/sub/LUI/AUIPC/MOP](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop/generated/layout.json) | 1 | 24 | 4 | 20 | 24 | 8 |
> | [jump/branch/compare](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/unrolled_circuits/jump_branch_slt/generated/layout.json) | 2 | 24 | 4 | 20 | 24 | 8 |
> | [shift/binary](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/unrolled_circuits/shift_binary/generated/layout.json) | 3 | 24 | 4 | 20 | 24 | 8 |
> | [unsigned multiply/divide](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/unrolled_circuits/mul_div_unsigned/generated/layout.json) | 4 | 23 | 4 | 19 | 23 | 8 |
> | [word memory](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/unrolled_circuits/load_store_word_only/generated/layout.json) | 16 | 24 | 4 | 20 | 24 | 8 |
> | [subword memory](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/unrolled_circuits/load_store_subword_only/generated/layout.json) | 17 | 24 | 4 | 20 | 24 | 8 |
> | [unified instructions](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/unrolled_circuits/unified_reduced_machine/generated/layout.json) | 128 | 23 | 4 | 19 | 23 | 10 |
> | [standalone IT](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/unrolled_circuits/inits_and_teardowns/generated/layout.json) | 255 | 24 | 3 | 20 | 23 | 2 |
> | [BLAKE2s](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/blake2_with_compression/generated/layout.json) | 0x7c7 | 20 | 8 | 16 | 24 | 6 |
> | [bigint](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/bigint_with_control/generated/layout.json) | 0x7ca | 22 | 6 | 18 | 24 | 8 |
> | [Keccak special5](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/keccak_special5/generated/layout.json) | 0x7cb | 22 | 6 | 18 | 24 | 6 |
> | [Keccak theta/rho](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/keccak_theta_rho/generated/layout.json) | 0x7cc | 22 | 6 | 18 | 24 | 6 |
> | [Keccak column parity](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/keccak_column_parity/generated/layout.json) | 0x7cd | 22 | 5 | 18 | 23 | 6 |
> | [Keccak chi5](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/circuit_defs/keccak_chi5/generated/layout.json) | 0x7ce | 22 | 5 | 18 | 23 | 6 |
>
> **Program setup caps (Algorithm 1a, base/continuation):**
>
> | $\mathrm{profile}$ | $\mathrm{mode}$ | Instruction-family IDs, in order | Setup-cap count |
> |---|---|---|---|
> | Unrolled | Base | 1, 2, 3, 4, 16, 17 | 6 |
> | Unrolled | Continuation | 1, 2, 3, 16 | 4 |
> | Unified | Base or continuation | 128 (unified) | 1 |
>
> **Other family identifiers:** standalone IT uses 255. Delegation types BLAKE2s, bigint, Keccak special5, theta/rho, column parity and chi5 use their fixed CSR numbers: 0x7c7, 0x7ca, 0x7cb, 0x7cc, 0x7cd and 0x7ce, respectively.
>
> In base/continuation mode, `ProgramSetupCaps` contains one cap per selected instruction family, including families with zero chunks. Neither its count nor its family list is sent in the proof. $\mathrm{commitment\text{-}config}$ does not change this selection.
>
> 1. For $\mathrm{chunk\text{-}config}=\mathrm{standard}$, select the ordered instruction-family list from the table above and the other families from their fixed identifiers. For $\mathrm{chunk\text{-}config}=\mathrm{terminal\text{-}wrapper}$, use the [Proth120 unified circuit](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json). From $C$, take the trace dimension $n$, memory/witness/committed-setup widths $(c_M,c_W,c_S)$, output-table count $s$ and order, and GKR layer relations and counts.
> 2. For $\mathrm{chunk\text{-}config}=\mathrm{standard}$, use BabyBear, $\mathrm{pack}=1$ and shared memory challenges. Select a parameter row:
>
>    - **$\mathrm{commitment\text{-}config}=\mathrm{ordinary}$:** select ordinary parameters by $n\in\{20,21,22,23,24\}$.
>    - **$\mathrm{commitment\text{-}config}=\mathrm{merged\text{-}feeder}$:** for the unified instruction circuit, require continuation $\mathrm{mode}$ and $n=23$, then select merged-feeder. Standalone IT and delegation chunks select ordinary parameters by $n\in\{20,21,22,23,24\}$.
>
>    For $\mathrm{chunk\text{-}config}=\mathrm{terminal\text{-}wrapper}$, use Proth120 for one chunk without delegation calls, with $n=22$, $\mathrm{pack}=16$ and the terminal wrapper row.
>
>    Use the selected field's transcript rules defined above and the same hash for Merkle commitments. Unsupported combinations have no Verifier instance.
> 3. Set cap size $h$ to 16 hashes for BabyBear and 8 for Proth120. For the ordinary and packed-delegation rows, `MemoryCaps`, `WitnessCaps` and `SetupCaps` commit the nonempty groups $M,W,S$, respectively. For the merged-feeder and terminal wrapper rows, `MemoryCaps` commits $M\mathbin{\|}W$, `SetupCaps` commits $S$ and `WitnessCaps` is empty. Each nonempty group has one cap. Use the fixed column order within each group and batch the resulting polynomial claims in memory/witness/setup order.
> 4. Set $N=n+\log_2(\mathrm{pack})$. For each round $r$, set $m_r=N-\sum_{i<r}k_i$, $|D_r|=2^{m_r}L_r$, leaf values per committed polynomial to $2^{k_r}$ and path depth to $\log_2|D_r|-k_r-\log_2h$. Base leaves contain base-field values; later leaves contain elements of $E$. Use the fixed domain generator and tree ordering. Require power-of-two domains, $L_r\ge2$, $1\le k_r\le m_r$, $h2^{k_r}\le|D_r|$, $m_r-k_r\ge4$ before intermediate commitments and $1\le N-\sum_rk_r$. The maximum domain size is $2^{27}$ for BabyBear and $2^{31}$ for the terminal wrapper row. Set the final coefficient count to $2^{N-\sum_r k_r}$.
> 5. Set $\ell$ to the total number of committed polynomials after packing and $F=\lfloor\log_2|E|\rfloor$ (123 for BabyBear, 122 for Proth120). Set $D_{\mathrm{lookup}}=(a2^n+T)\max(1,c_S)$, where $a$ counts lookup accesses per row and $T$ counts committed-table entries plus the $2^{16}$ range table and $2^{19}$ timestamp table when used. With $B(x)=\lceil\log_2\max(1,x)\rceil$, select:
>
>    $$
>    \begin{aligned}
>    \ell_{\mathrm{lookup}}&=\max(0,100-\max(0,F-B(D_{\mathrm{lookup}}))) \\
>    \ell_{\mathrm{batch}}&=\max(0,100-\max(0,F-N-\log_2L_0-B(\ell)))
>    \end{aligned}
>    $$
>
>    Use $\ell_{\mathrm{lookup}}$ for the lookup-PoW threshold in Algorithm 3a, step 4, and $\max(20,\ell_{\mathrm{lookup}})$ for the combined memory/lookup-PoW threshold in Algorithm 1b, step 3. Use $\ell_{\mathrm{batch}}$ for the batching-PoW threshold in Algorithm 3b, step 3.
>
> 6. Return the ordered instruction-family list where applicable, and the selected field, transcript, commitment layout, column-packing factor, schedules, sizes and PoW thresholds.
>
> **Packed-delegation fixture.** The packed-delegation fixture uses the following fixed parameters for standalone chunk proving and verification: the [blake2_with_extended_control circuit](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json), BabyBear, shared memory challenges, $n=20$, $\mathrm{pack}=16$ and the packed-delegation row below. Its commitment layout and derived parameters follow steps 3–5. Before drawing the packing coordinates, both parties hash $T_{\mathrm{chunk}}$'s current seed once with seven-round BLAKE2s.
>
> **Parameter rows:** $\mathbf{L}=(L_0,L_1,\ldots)$ lists base then intermediate expansion factors; $\mathbf{k},\mathbf{t},\mathbf{b}$ list folds, query counts and PoW bits per round.
>
> | Family | $n$ | $\mathbf{k}$ | $\mathbf{L}$ | $\mathbf{t}$ | $\mathbf{b}$ |
> |---|---|---|---|---|---|
> | Ordinary | 20 | (1,5,5,4,4) | (2,256,8192,32768,524288) | (89,11,7,6,5) | (26,27,25,25,21) |
> | Ordinary | 21 | (1,5,5,5,4) | (2,64,2048,32768,524288) | (89,15,8,6,5) | (26,25,27,25,21) |
> | Ordinary | 22 | (1,5,5,5,5) | (2,64,2048,32768,524288) | (89,15,8,6,5) | (26,25,27,25,21) |
> | Ordinary | 23 | (1,5,5,5,4) | (2,16,512,16384,524288) | (89,23,10,7,5) | (26,24,25,19,21) |
> | Ordinary | 24 | (1,5,5,5,4,3) | (2,16,512,16384,524288,524288) | (89,23,10,7,5,5) | (26,24,25,19,21,21) |
> | Merged-feeder | 23 | (1,5,5,5,4) | (16,32,1024,32768,1048576) | (21,17,9,5,4) | (29,26,25,26,21) |
> | Packed-delegation | 20 | (1,5,5,5,4,3) | (2,16,512,16384,524288,524288) | (89,23,10,7,5,5) | (26,24,25,19,21,21) |
> | Terminal wrapper | 22 | (2,4,4,4,4,4) | $(2^5,2^7,2^{11},2^{15},2^{19},2^{23})$ | (17,12,8,6,5,4) | (30,30,27,25,21,24) |
>
> Packed-delegation sources: [packed fixture configuration](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/verifier_common/src/test_circuits.rs#L175), [proving fixture](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/prover/src/tests/gkr/family_circuits.rs#L92), [packed parameter constructor](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/prover/src/gkr/prover_config/example_configs.rs#L206), [Verifier fixture](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/verifier_generator/tests/packed_verify.rs#L20).
>
> Terminal sources: [terminal parameter configuration](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/prover/src/gkr/prover_config/example_configs.rs#L227), [terminal prover selection](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/program_prover/src/l1.rs#L77), [Keccak Merkle hashing](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/prover/src/merkle_trees/keccak256_for_everything_tree.rs#L1), [operation modes](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/prover/src/gkr/prover/mod.rs#L72), [standalone transcript seed](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/verifier_evm/src/seed.rs#L22), [Proth120 field](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/field/src/proth120.rs#L4), [Keccak transcript](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/transcript/src/keccak256.rs#L64).

---

**References:** [GKR](https://people.cs.georgetown.edu/jthaler/GKRNote.pdf), [LogUp](https://eprint.iacr.org/2022/1530), [GKR lookup compression](https://eprint.iacr.org/2023/1284), [WHIR](https://eprint.iacr.org/2024/1586), [Two Shuffles Make a RAM](https://eprint.iacr.org/2023/1115).

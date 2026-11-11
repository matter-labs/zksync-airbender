---
class: protocol-appendix-light
---

# Appendix — Protocol algorithms and soundness

Parameter reference: `Sec100`, `av_gkr_compiler` at [`c1a6622`](https://github.com/matter-labs/zksync-airbender/commit/c1a662222cafcd96db4383dce737edb79fa62b09).

```text
FullStatement (1a)
  ├─ VerifyChunks → Chunk → SeededChunk → GKR layers → OutputChecks → WHIR
  ├─ CloseMemory → equal event multisets → machine execution
  └─ FinishChain → (application result, program-history digest)
TerminalStatement (1b) → SeededChunk → CloseMemory → (application result, program-history digest)
Recursive step: prove the execution of FullStatement; repeat.
```

> **Fiat–Shamir challenges**
>
> **Parameters:**
>
> - **BabyBear:** seven-round BLAKE2s with messages absorbed as raw 32-bit words. $E$ is BabyBear's quartic extension, with base modulus $p=2^{31}-2^{27}+1$.
> - **Proth120:** Keccak256 with field elements encoded as canonical 16-byte big-endian values and 32-bit messages, including boundary-state and Merkle-cap digest words, encoded little-endian. $E$ is the prime field with modulus $q=7\cdot2^{120}+1$. Each subsequent absorption of an encoded message $m$ updates the seed as $S\leftarrow\mathrm{Keccak256}(S\mathbin{\|}m)$.
>
> **Proof of work (PoW).** When challenge drawing requires $b$ bits of proof of work, Prover supplies a 64-bit nonce (encoded as eight big-endian bytes for Proth120), which both parties absorb into the transcript immediately before drawing. The first output word, 32 bits for BabyBear or 256 bits for Proth120, is reserved for PoW: Verifier accepts only if it has $b$ leading zero bits, and field challenges are sampled from subsequent drawn words. For Proth120 and only when sampling WHIR queries, the first 32-bit word following the 256-bit PoW digest is additionally discarded. At $b=0$, except for WHIR OOD draws (Algorithm 7, step 2.2) and WHIR sumcheck folding challenges (Algorithm 8, QuadraticStep, step 2), the nonce is still absorbed and the PoW word skipped, so every nonce passes.
>
> **Transcript flow across FullStatement.** In base/continuation mode, `FullStatement` first absorbs the final state (register values, PC and timestamps) and all chunks' memory commitments (Merkle tree caps), with circuit-family identifiers and RAM initialization/teardown window identifiers. These identify the circuit types and RAM ranges associated with the commitments. Before absorbing a Merkle-cap sequence, it zero-pads to the next block boundary; successive absorb calls otherwise concatenate without padding. This precommitment binds the selected memory events before the shared challenges $\mathbf{r}_{\mathrm{mem}}$ are drawn (Algorithms 1a and 2).
>
> Each chunk starts a fresh transcript by absorbing its window identifiers, $\mathbf{r}_{\mathrm{mem}}$, and commitments to its setup, memory and remaining witness, omitting absent witness groups (Algorithm 3a). Chunk transcripts proceed in parallel through GKR and WHIR; in the end, chunks' verified memory products are combined without further challenges.
>
> Prover prepares the memory commitments and computes the shared challenges before emitting the proof. Verifier reconstructs the memory transcript during `VerifyChunks` and authenticates the supplied challenges afterward.
>
> The `TerminalStatement` (Algorithm 1b) variant instead initializes one transcript by absorbing the final state, window identifiers, setup cap and merged memory/witness cap. After the combined memory/lookup PoW, both parties draw $\mathbf{r}_{\mathrm{mem}}$ followed by $\mathbf{r}_{\mathrm{lookup}}$ and continue that same transcript through GKR and WHIR.
>
> **Modular reduction sampling.** For BabyBear, each base-field challenge is a drawn 32-bit word reduced modulo $p$. Each extension-field challenge combines four such samples as coefficients in a fixed basis of $E$. Assuming independent uniform transcript words, each reduced coefficient has at most three preimages.
>
> For Proth120, let $S_0$ be the transcript seed before drawing. For each successive challenge $i\ge1$, compute $S_i=\mathrm{Keccak256}(S_{i-1})$ and reduce the first 128 bits of $S_i$, interpreted as a big-endian integer, modulo $q$. Retain $S_i$ as the seed for the next transcript operation. Assuming independent uniform hash outputs, each reduced field element has at most $\lceil2^{128}/q\rceil=37$ preimages among the 128-bit inputs.
>
> Assuming independent uniform hash output, for any fixed $a\in E$:
>
> $$
> \Pr[\text{challenge}=a]\le\mu=
> \begin{cases}
> (3/2^{32})^4=81/2^{128}\approx 2^{-121.66}, & \text{BabyBear},\\
> \lceil2^{128}/q\rceil/2^{128}=37/2^{128}\approx 2^{-122.79}, & \text{Proth120}.
> \end{cases}
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
> 6. Return $\mathrm{FinishChain}(\mathtt{ProgramSetupCaps},\mathrm{fin},\mathrm{mode})$ (Algorithm 10): the application result $(x_{10},\ldots,x_{17})$ and program-history digest $(h_0,\ldots,h_7)$, each eight 32-bit words. Reject if any check or subalgorithm fails.
>
> **Algorithm 1b — TerminalStatement**
>
> **Configuration:** $\mathrm{chunk\text{-}config}=\mathrm{terminal\text{-}wrapper}$, with parameters from Algorithm 12.
>
> **Protocol**
>
> 1. Select circuit $C$ from Algorithm 12's terminal-wrapper entry. Prover sends $\mathrm{fin}$ in the 99-word format from Algorithm 1a, step 1, followed by two RAM initialization/teardown window identifiers $b$ as 32-bit values, then setup caps `SetupCaps` and memory caps `MemoryCaps`. The number of caps in each group and the number of hashes per cap are specified in Algorithm 12's terminal-wrapper entry.
> 2. Both parties initialize $T_{\mathrm{mem{+}}}$ with seed $\mathrm{Keccak256}(\mathrm{fin}\mathbin{\|}b\mathbin{\|}\mathtt{SetupCaps}\mathbin{\|}\mathtt{MemoryCaps})$, encoding the concatenation as little-endian 32-bit words.
> 3. Prover sends the 64-bit memory/lookup-PoW nonce. Both parties absorb it into $T_{\mathrm{mem{+}}}$ and draw one 256-bit PoW word. Verifier requires the number of leading zero bits to meet the combined memory/lookup-PoW threshold specified in Algorithm 12. Both parties then sample $\mathbf{r}_{\mathrm{mem}}=(r_{\mathrm{mem},0},\ldots,r_{\mathrm{mem},5},r_{\mathrm{mem},\eta})\in E^7$, followed by $\mathbf{r}_{\mathrm{lookup}}=(r_{\mathrm{lookup},\alpha},r_{\mathrm{lookup},\beta})\in E^2$, from subsequent drawn words.
> 4. Run $\mathrm{SeededChunk}(C,\mathbf{r}_{\mathrm{mem}},\mathbf{r}_{\mathrm{lookup}},b,(\mathtt{MemoryCaps},\varnothing,\mathtt{SetupCaps}),T_{\mathrm{mem{+}}})$ (Algorithm 3b), obtaining $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$ and $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$, together with the updated $T_{\mathrm{mem{+}}}$.
> 5. Run $\mathrm{CloseMemory}(\mathrm{fin},\mathbf{r}_{\mathrm{mem}},\mathrm{RS}_{\mathrm{chunk}}\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{chunk}}\mathrm{WS}_{\mathrm{IT}})$ (Algorithm 9).
> 6. Return from $\mathrm{fin}$: the application result $(x_{10},\ldots,x_{17})$ and program-history digest $(h_0,\ldots,h_7)=(x_{18},\ldots,x_{25})$, each eight 32-bit words. Reject if any check or subalgorithm fails.
>
> **Soundness — statement composition (conditional)**
>
> **Standard path (Algorithm 1a; adapted).** For base/continuation mode, assume commitment binding, Algorithm 2's participant-binding lemma, and Algorithm 9's event-encoding and execution-reconstruction premises. Outside the chunk-verification failure events, all accepted chunks satisfy their local relations and export the correct selected memory-event products. Participant binding fixes the event multisets before memory-challenge sampling; Algorithm 1a, step 4 authenticates the supplied challenges against that transcript. Algorithm 9 then bounds acceptance of unequal read/write multisets by $\varepsilon_{\mathrm{mem}}\le N\mu$. If the multisets are equal, their boundary conditions and the local relations jointly imply an execution ending at $\mathrm{fin}$. Thus false execution acceptance requires a chunk-verification failure or a memory-fingerprint collision, giving
>
> $$
> \varepsilon_{\mathrm{exec}}\le\varepsilon_{\mathrm{mem}}+\sum_i\varepsilon_{\mathrm{chunk},i}.
> $$
>
> Here $\varepsilon_{\mathrm{chunk},i}$ includes all local lookup, GKR and PCS errors of Algorithm 3b, counted once, with the sum bounded over permitted participant collections. Each component bound must hold for adversarial choices conditioned on the preceding transcript and no earlier soundness failure. The resulting execution claim is relative to the supplied setup identities; Algorithms 10–11 bind the program history and anchor the recursive executions to the expected program identities and successful endpoints.
>
> **Terminal path (Algorithm 1b; conditional).** Algorithm 1b fixes one circuit and absorbs $\mathrm{fin}$, window identifiers and setup/memory caps before drawing the memory and lookup challenges, then invokes the shared local verification in Algorithm 3b. Applying the same local-verification and memory-closure decomposition requires terminal-specific memory-table/event binding, event-count and Algorithm 9 reconstruction premises; Algorithm 2's participant-binding argument is not invoked. These remain proof obligations, together with the packed-claim reduction and configuration-specific opening guarantees identified below. Algorithm 11 supplies the terminal identity/history comparisons and recursive handoff premises; Algorithm 1b does not run Algorithm 10's history update.
>
> These component bounds enter the whole-system Fiat–Shamir analysis described in the final soundness section.

---

> **Algorithm 2 — VerifyChunks**
>
> **Configuration:** Inherit $\mathrm{profile}$, $\mathrm{mode}$ and $\mathrm{commitment\text{-}config}$ from Algorithm 1a.
>
> **Input:** `ProgramSetupCaps` Merkle tree caps, $\mathbf{r}_{\mathrm{mem}}$ challenges, and the running memory transcript $T_{\mathrm{mem}}$ initialized with $\mathrm{fin}$. **Output:** accumulated read/write products $\mathrm{RS},\mathrm{WS}\in E$ and $T_{\mathrm{mem}}$ extended with the participating memory commitments and identifiers.
>
> **Protocol**
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
>       1. Verifier runs $\mathrm{Chunk}(C,\mathbf{r}_{\mathrm{mem}})$† (Algorithm 3a), obtaining the chunk's main read/write products $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$, the additional initialization/teardown products $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$ for unified instruction chunks, memory caps `MemoryCaps`, setup caps `SetupCaps` and window identifiers $b$.
>
>          † _Chunk calls may run in parallel, each consuming the separate, non-overlapping portion of proof data corresponding to that chunk._
>
>       2. Verifier checks the returned outputs according to $C$:
>
>          - **Unrolled instruction circuit:** require $b$ to be empty and `SetupCaps` to match the cap for $C$ in `ProgramSetupCaps`.
>          - **Unified instruction circuit:** require two window identifiers in $b$ and `SetupCaps` to match the cap for $C$ in `ProgramSetupCaps`. For the first $n-n_{\mathrm{IT}}$ chunks, require $b=(0,0)$. Across the final $n_{\mathrm{IT}}$ chunks, require the window identifiers, in proof order, to form a strictly increasing sequence in $[0,64)$.
>          - **Standalone IT circuit:** require eight window identifiers in $b$ and require the identifiers, in proof order across chunks, to form a strictly increasing sequence in $[0,64)$. This circuit has no committed setup tables, so `SetupCaps` is empty and requires no comparison.
>          - **Delegation circuit:** require $b$ to be empty and `SetupCaps` to match the Verifier's hardcoded cap for $C$.
>
>       3. Both parties absorb the following into $T_{\mathrm{mem}}$, using $C$'s 32-bit family label from Algorithm 12:
>
>          - **Unrolled instruction or delegation circuit:** if this is the first chunk for $C$, absorb its family label padded with fifteen zero words. Then absorb this chunk's `MemoryCaps`.
>          - **Standalone IT circuit:** if this is the first chunk for $C$, absorb its family label padded with fifteen zero words. Then absorb this chunk's `MemoryCaps`, followed by its eight window identifiers $b$ padded with eight zero words.
>          - **Unified instruction circuit:** absorb $C$'s family label and this chunk's two window identifiers $b$, padded with thirteen zero words. Then absorb this chunk's `MemoryCaps`.
>       4. Update $\mathrm{RS}\leftarrow\mathrm{RS}\cdot\mathrm{RS}_{\mathrm{chunk}}$ and $\mathrm{WS}\leftarrow\mathrm{WS}\cdot\mathrm{WS}_{\mathrm{chunk}}$. For the final $n_{\mathrm{IT}}$ unified instruction chunks, Verifier also updates $\mathrm{RS}\leftarrow\mathrm{RS}\cdot\mathrm{RS}_{\mathrm{IT}}$ and $\mathrm{WS}\leftarrow\mathrm{WS}\cdot\mathrm{WS}_{\mathrm{IT}}$.
> 3. Verifier requires the following memory-term capacity bounds, using the fixed circuit parameters listed before Algorithm 12. The bounds count only one side of the memory argument ($\mathrm{RS}$ or $\mathrm{WS}$), for soundness analysis purposes:
>
>    - **Instruction cycles $<2^{36}$:** count each unrolled instruction chunk by its trace rows, or each unified instruction chunk as $2^{24}$ cycles.
>    - **Non-IT memory-argument terms $<2^{40}$:** For each instruction chunk, count four terms per cycle (the fixed bound used for all instruction circuits), using the cycle count specified above. For each delegation chunk, count its rows multiplied by its terms per row, using the fixed circuit parameters listed before Algorithm 12. Sum these contributions across all instruction and delegation chunks and require the total to be below $2^{40}$.
>
>    The remaining contributions are accounted for separately:
>
>    - **Standalone-IT memory-argument terms $\le 2^{30}$:** this follows from the earlier limit of eight chunks and the fixed eight windows of $2^{24}$ terms per chunk (listed before Algorithm 12).
>    - **Unified-IT memory-argument terms $\le 2^{29}$:** the identifier checks permit at most 64 distinct windows, each contributing $2^{23}$ terms (listed before Algorithm 12).
>    - **33 machine-state boundary terms:** Algorithm 9, step 1 adds 33 initialization writes to $\mathrm{WS}$ and 33 final-state reads to $\mathrm{RS}$, one for each register and the PC.
>
> 4. Return $\mathrm{RS},\mathrm{WS},T_{\mathrm{mem}}$.
>
> **Soundness — participant/window binding (new, conditional).** Assume Algorithm 3b's local correctness. The required precommitment guarantee links the participating circuits, their memory data and window identifiers to the memory events tested by Algorithm 9, before the shared memory challenges are sampled. Participant interpretation despite the omitted proof counts, and memory-table binding exported by Algorithm 7 through Algorithm 3b, are the two parts of this requirement. Both remain conditional imports here. Together they justify the fingerprint analysis; local circuit correctness and Algorithm 9's memory-consistency and reconstruction arguments then connect the accepted events to the claimed computation.
>
> For each fixed circuit, its committed memory columns and window identifiers determine the exported events. Addresses, values, timestamps and execution selectors come from those columns or fixed circuit constants; initialization/teardown addresses combine the window identifiers with fixed virtual row addresses. The circuit's access layout and execution selectors determine multiplicities and inactive-row contributions. Program setup and separate witness columns constrain whether these values satisfy the circuit, but cannot change the exported events in a locally correct completion with the same memory columns, circuit and identifiers. This explains why their omission from the memory prefix preserves the events under the stated binding assumptions.
>
> The bound participant list fixes the chunk counts. For unified chunks, excluded identifier pairs are $(0,0)$ and selected pairs are strictly increasing, so the identifiers fix the contributing suffix. The absorbed final state fixes Algorithm 9's register/PC boundary events. Algorithm 2 therefore accumulates the prescribed products of events fixed before the shared challenges; its capacity accounting bounds their number. After Algorithm 1a authenticates those challenges, Algorithm 9 supplies the memory-fingerprint bound and the event-encoding, RAM-boundary-coverage and execution-reconstruction premises.
>
> **TODO — numerical composition:** after resolving participant binding and Algorithm 7's memory-table binding export, account for any candidate-list or alternative-interpretation losses, combine them with the imported local and memory-fingerprint errors, and charge each failure once.
>
> **Retained draft obligations (to reconcile with the argument above):**
>
> Required participant-binding lemma: under commitment binding, for each fixed memory-transcript prefix immediately before the nonce, all completions satisfying the local chunk relations and participant checks induce the same selected read/write event multisets, including multiplicities and Algorithm 9's boundary events, independently of the subsequently sampled memory challenges. Its proof must establish that the encoding fixes the participating caps and their interpretation sufficiently to determine these multisets. In particular, proof counts, `ProgramSetupCaps` and separate witness caps are omitted from this prefix: varying them while preserving the prefix must not change event selection, tuple values or multiplicities. Later absorption of setup/witness caps into chunk transcripts does not establish this earlier binding. This lemma remains a proof obligation.
>
> For unified chunks, the authenticated window identifiers determine which IT products contribute: excluded chunks have $b=(0,0)$, whereas selected chunks have strictly increasing identifiers. Once the ordered chunk list and its identifiers are bound, these conditions uniquely determine the selected suffix and $n_{\mathrm{IT}}$. Establishing that the selected IT windows supply every RAM boundary required by the execution remains part of Algorithm 9's reconstruction lemma.
>
> Outside local verification failures, setup-cap equality ties instruction chunks to the supplied program setups and delegation chunks to the fixed delegation setups. Circuit-bound, strictly increasing IT windows exclude repeated initialization/teardown windows; complete coverage remains a premise of Algorithm 9's reconstruction lemma. The capacity argument must additionally show that the charged counts bound all selected events, including IT and boundary events in the final $N$ bound. Subject to these obligations, the accumulated products are fingerprints of the fixed multisets, so Algorithm 9's collision bound applies after Algorithm 1a authenticates the shared challenges.

---

> **Algorithm 3 — Chunk preparation and verification**
>
> For standard verification, Algorithm 2 calls Algorithm 3a, which prepares the chunk and invokes Algorithm 3b. Terminal verification uses Algorithm 1b's preparation and then calls Algorithm 3b directly.
>
> **Algorithm 3a — Chunk**
>
> **Configuration:** $\mathrm{chunk\text{-}config}=\mathrm{standard}$; inherit $\mathrm{profile}$, $\mathrm{mode}$ and $\mathrm{commitment\text{-}config}$ from Algorithm 2.
>
> **Input:** compiled arithmetic circuit $C$ and memory challenges $\mathbf{r}_{\mathrm{mem}}$. **Output:** read/write products $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$, the additional initialization/teardown products $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$ for unified instruction chunks, memory caps `MemoryCaps`, setup caps `SetupCaps` and window identifiers $b$.
>
> **Protocol**
>
> 1. Prover sends the RAM initialization/teardown window identifiers $b$ as 32-bit values according to $C$:
>
>    - **Standalone IT circuit:** eight values.
>    - **Unified instruction circuit:** two values.
>    - **Otherwise:** $b$ is empty and no values are sent.
>
> 2. Prover sends `SetupCaps`, `MemoryCaps` and `WitnessCaps`, in that order. The number of caps in each group and the number of hashes per cap are specified in Algorithm 12 for $C$ and the inherited $(\mathrm{profile},\mathrm{mode},\mathrm{commitment\text{-}config})$ configuration parameters.
>
> 3. Both parties start a fresh transcript $T_{\mathrm{chunk}}$ by absorbing the ordered prefix below:
>
>    $$
>    b\mathbin{\|}\mathbf{r}_{\mathrm{mem}}\mathbin{\|}\mathtt{SetupCaps}\mathbin{\|}\mathtt{MemoryCaps}\mathbin{\|}\mathtt{WitnessCaps}
>    $$
>
> 4. Prover sends the 64-bit lookup-PoW nonce. Both parties absorb it into $T_{\mathrm{chunk}}$ and draw one 32-bit PoW word. Verifier requires the number of leading zero bits to meet the lookup-PoW threshold specified in Algorithm 12. Both parties then sample the lookup challenges $\mathbf{r}_{\mathrm{lookup}}=(r_{\mathrm{lookup},\alpha},r_{\mathrm{lookup},\beta})\in E^2$ from subsequent words.
> 5. Run $\mathrm{SeededChunk}(C,\mathbf{r}_{\mathrm{mem}},\mathbf{r}_{\mathrm{lookup}},b,(\mathtt{MemoryCaps},\mathtt{WitnessCaps},\mathtt{SetupCaps}),T_{\mathrm{chunk}})$ (Algorithm 3b), obtaining $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$, the additional pair $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$ when present, and the updated $T_{\mathrm{chunk}}$.
> 6. Return $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$ and $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$, when present, from step 5, together with `MemoryCaps`, `SetupCaps` and $b$ from steps 1–2.
>
> **Algorithm 3b — SeededChunk**
>
> **Configuration:** $\mathrm{chunk\text{-}config}\in\{\mathrm{standard},\mathrm{terminal\text{-}wrapper}\}$, fixed to $\mathrm{standard}$ by Algorithm 3a and $\mathrm{terminal\text{-}wrapper}$ by Algorithm 1b. For $\mathrm{standard}$, inherit $\mathrm{profile}$, $\mathrm{mode}$ and $\mathrm{commitment\text{-}config}$ from Algorithm 3a.
>
> **Input:** compiled arithmetic circuit $C$, memory challenges $\mathbf{r}_{\mathrm{mem}}$, lookup challenges $\mathbf{r}_{\mathrm{lookup}}$, window identifiers $b$, cap groups $(\mathtt{MemoryCaps},\mathtt{WitnessCaps},\mathtt{SetupCaps})$ and the prepared transcript $T_{\mathrm{chunk}}$. **Output:** read/write products $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$, the additional initialization/teardown products $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$ for unified instruction chunks, and the updated transcript $T_{\mathrm{chunk}}$.
>
> **Protocol**
>
> 1. Both parties run GKR:
>
>    1. Prover sends $s$ claimed output tables $A_0,\ldots,A_{s-1}$ of $C$, each containing sixteen elements of $E$, with $s$ and the table order specified by $C$'s output layout in Algorithm 12. Both parties absorb the tables into $T_{\mathrm{chunk}}$ as one concatenated message in that order, then sample the GKR evaluation point $\mathbf{z}_{\mathrm{gkr}}=(z_{\mathrm{gkr},0},\ldots,z_{\mathrm{gkr},3})\in E^4$ and batching challenge $r_{\mathrm{batch},\mathrm{gkr}}\in E$.
>    2. Initialize $\mathbf{a}_{\mathrm{gkr}}\leftarrow(\mathrm{MLE}(A_0)(\mathbf{z}_{\mathrm{gkr}}),\ldots,\mathrm{MLE}(A_{s-1})(\mathbf{z}_{\mathrm{gkr}}))$, where $\mathrm{MLE}(A)$ is $A$'s multilinear extension.
>    3. Let $2^n$ be $C$'s trace row count from Algorithm 12. Process $C$'s compression layers for $k=4,\ldots,n-1$, followed by its main layers from outputs towards inputs. For each layer $C_{\mathrm{layer}}$, update using Algorithm 4:
>
>       $$
>       ((\mathbf{z}_{\mathrm{gkr}},\mathbf{a}_{\mathrm{gkr}}),r_{\mathrm{batch},\mathrm{gkr}},T_{\mathrm{chunk}})\leftarrow\mathrm{GKRLayer}(C_{\mathrm{layer}},(\mathbf{z}_{\mathrm{gkr}},\mathbf{a}_{\mathrm{gkr}}),r_{\mathrm{batch},\mathrm{gkr}},\mathbf{r}_{\mathrm{mem}},\mathbf{r}_{\mathrm{lookup}},b,T_{\mathrm{chunk}}).
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
> 2. Run $\mathrm{OutputChecks}(A_0,\ldots,A_{s-1})$ (Algorithm 6), obtaining the read/write products $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$ and, if $C$ is the unified instruction circuit, the additional initialization/teardown products $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$.
>
> 3. Prover sends the 64-bit batching/proximity-PoW nonce. Both parties absorb it into $T_{\mathrm{chunk}}$ and draw one 32-bit PoW word (256-bit for Proth120 transcript). Verifier requires the number of leading zero bits to meet the batching-PoW threshold specified in Algorithm 12 for $C$ and the selected configuration. Both parties then sample the WHIR batching challenge $r_{\mathrm{batch},\mathrm{whir}}\in E$ from subsequent words.
>
> 4. Set $T_{\mathrm{chunk}}\leftarrow\mathrm{WHIR}((\mathtt{MemoryCaps},\mathtt{WitnessCaps},\mathtt{SetupCaps}),(\mathbf{z}_{\mathrm{whir}},\mathbf{a}_{\mathrm{whir}}),r_{\mathrm{batch},\mathrm{whir}},T_{\mathrm{chunk}})$ (Algorithm 7).
>
> 5. Return $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$, the additional pair $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$ when present, and the updated $T_{\mathrm{chunk}}$.
>
> **Soundness — chunk verification (conditional)**
>
> **Preparation premises.** Algorithm 3a supplies the standard prefix and lookup challenges; Algorithm 1b supplies the terminal prefix and both challenge sets. Algorithm 3b continues the supplied transcript without reinitialization. The local argument below assumes the required lookup-data binding before lookup sampling on either path; merely supplying a transcript does not establish that premise. Standard memory-challenge authentication and participant binding remain in Algorithms 1a and 2, while the terminal obligations are stated in Algorithm 1b's soundness discussion.
>
> **Shared local composition (Algorithm 3b; adapted, conditional).** Fix the circuit, layout and shared memory challenges. Assume binding commitments, the layer-reduction premises of Algorithm 4 and the opening guarantee of Algorithm 7. Lookup tuples, selectors, tables and multiplicities must be determined by committed columns or public data before $\mathbf{r}_{\mathrm{lookup}}$ is sampled. Outside the GKR and PCS failure events, the supplied output tables are the circuit's actual outputs and its zero constraints hold. Algorithm 6 then establishes lookup membership, except with error $\varepsilon_{\mathrm{lookup}}$, and returns the selected memory products. Hence
>
> $$
> \varepsilon_{\mathrm{chunk}}\le\varepsilon_{\mathrm{GKR}}+\varepsilon_{\mathrm{PCS}}+\varepsilon_{\mathrm{lookup}}.
> $$
>
> **Memory-table binding export (conditional).** For Algorithm 2, additionally import Algorithm 7's memory-table binding guarantee below: outside the accounted commitment/PCS failures, the memory columns used by the accepted local relations are fixed by the memory precommitment before $\mathbf r_{\mathrm{mem}}$ is sampled. The local correctness argument must use those same columns. Establishing this timing and consistency remains a proof obligation in Algorithm 7; any candidate-list alternative and its losses must be carried through to Algorithm 2's memory analysis.
>
> Algorithm 4 owns the algebraic verification of the product/rational compression trees; Algorithm 6 owns the lookup fingerprint error; Algorithm 7 owns base-claim batching and opening verification. Algorithm 1a uses the resulting local relation with Algorithm 2's event binding and Algorithm 9's reconstruction premises. The displayed bound covers the unpacked BabyBear path; packed variants require an additional reduction for the pack-coordinate claim merge.

---

> **Algorithm 4 — GKRLayer**
>
> **Input:** fixed circuit layer $C_{\mathrm{layer}}$, output evaluation point $\mathbf{z}_{\mathrm{gkr}}$ and claims $\mathbf{a}_{\mathrm{gkr}}$, batching challenge $r_{\mathrm{batch},\mathrm{gkr}}$, shared memory challenges $\mathbf{r}_{\mathrm{mem}}$, lookup challenges $\mathbf{r}_{\mathrm{lookup}}$, window identifiers $b$ and the running chunk transcript $T_{\mathrm{chunk}}$. **Output:** preceding-layer evaluation point $\mathbf{z}'_{\mathrm{gkr}}$, claims $\mathbf{a}'_{\mathrm{gkr}}$, next batching challenge $r'_{\mathrm{batch},\mathrm{gkr}}$, and the updated transcript $T_{\mathrm{chunk}}$.
>
> 1. Both parties batch the incoming claims $\mathbf{a}_{\mathrm{gkr}}$ via RLC using powers of $r_{\mathrm{batch},\mathrm{gkr}}$ in the order specified by $C_{\mathrm{layer}}$, obtaining the initial sumcheck claim $v_{\mathrm{batch}}$.
>
> 2. Run $\mathrm{EQSumcheck}((\mathbf{z}_{\mathrm{gkr}},v_{\mathrm{batch}}),T_{\mathrm{chunk}})$ (Algorithm 5) for the layer's batched gate polynomial, obtaining the sumcheck evaluation point $\mathbf{z}_{\mathrm{sumcheck}}$, scalar residual claim $v_{\mathrm{sumcheck}}$, final-coordinate EQ factor $e$ and updated transcript $T_{\mathrm{chunk}}$.
>
> 3. Prover sends $\mathbf{a}_{\mathrm{sumcheck}}$: claimed evaluations of all input polynomials required by $C_{\mathrm{layer}}$ and, for main layers only, cached relation outputs (including claimed virtual-setup polynomial evaluations), in $C_{\mathrm{layer}}$'s prescribed evaluation order.
>
> 4. Verifier evaluates the layer's gates from $\mathbf{a}_{\mathrm{sumcheck}}$:
>
>    - **Compression layer:** Verifier combines the pairwise claimed evaluations at $(0,\mathbf{z}_{\mathrm{sumcheck}})$ and $(1,\mathbf{z}_{\mathrm{sumcheck}})$ using the layer's memory-product or rational-sum LogUp accumulation relations.
>
>    - **Main layer:** Verifier uses the gate-input evaluations at $\mathbf{z}_{\mathrm{sumcheck}}$, including cached relation outputs where applicable, to evaluate copy/linear relations, quadratic arithmetic, memory-product and lookup relations (using $\mathbf{r}_{\mathrm{mem}}$, $\mathbf{r}_{\mathrm{lookup}}$ and $b$ where required), and zero-constraint expressions as specified by $C_{\mathrm{layer}}$'s gates. Verifier also evaluates the cached relations using claimed inputs from $\mathbf{a}_{\mathrm{sumcheck}}$ where needed and computes virtual lookup-table expressions directly at $\mathbf{z}_{\mathrm{sumcheck}}$. He requires the claimed cached outputs, including virtual setup evaluations, to equal the corresponding computed values.
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
>
> **Soundness — layer reduction and GKR budget (adapted, conditional).** Assume the fixed layer wiring and auxiliary identities implement the claimed gate relation, its batched gate polynomial satisfies Algorithm 5's degree bound, and each claimed value is fixed before the challenge testing it. Algorithm 5 reduces a false batched output claim to a false gate evaluation. The gate check then forces a false preceding-layer claim; auxiliary and public-polynomial checks must establish the identities used in this implication. In a compression layer, fixed endpoint discrepancies define a nonzero linear polynomial in $z_{\mathrm{sumcheck},\mathrm{pair}}$, so interpolation hides them with probability at most $\mu$. Induction through the layers terminates at the base openings established by Algorithm 7.
>
> For the complete GKR path in Algorithm 3b, a false sixteen-entry output table survives evaluation at $\mathbf{z}_{\mathrm{gkr}}\in E^4$ with probability at most $4\mu$; batching $b$ fixed scalar claims costs at most $(b-1)\mu$. Let $B$ be the sum of all power-batching degrees, including the initial output batch; $R$ the total number of EQSumcheck rounds; $Z\le R$ the charged EQ-zero events; and $S$ the sum of the remaining point/line-test degrees, including endpoint interpolation. Then
>
> $$
> \varepsilon_{\mathrm{GKR}}\le\min(1,\mu(4+B+3R+Z+S)).
> $$
>
> For $L$ main layers each using $n$ rounds, $R=\sum_{k=4}^{n-1}k+Ln$. These are proof-accounting quantities determined by the selected circuit. Completing the bound requires the layer/auxiliary-relation induction and explicit $B,R,Z,S$ counts for that circuit; lookup fingerprinting and base-opening errors are composed in Algorithm 3b.

---

> **Algorithm 5 — EQSumcheck**
>
> **Configuration:** polynomial $G$ of individual degree $\le 2$, available to Prover.
>
> **Input:** incoming point $\mathbf{z}_{\mathrm{gkr}}\in E^k$, batched claim $v_{\mathrm{batch}}$ and the running chunk transcript $T_{\mathrm{chunk}}$. **Output:** point $\mathbf{z}_{\mathrm{sumcheck}}\in E^k$, scalar residual claim $v_{\mathrm{sumcheck}}$, final-coordinate EQ factor $e$, and the updated transcript $T_{\mathrm{chunk}}$.
>
> **Notation:** The Boolean-cube interpolation kernel is $\mathrm{eq}(\mathbf{u},\mathbf{x})=\prod_j((1-u_j)(1-x_j)+u_jx_j)$. The incoming claim is $v_{\mathrm{batch}}=\sum_{\mathbf{x}\in\{0,1\}^k}\mathrm{eq}(\mathbf{z}_{\mathrm{gkr}},\mathbf{x})G(\mathbf{x})$.
>
> 1. Both parties initialize $e\leftarrow1$ and $v_{\mathrm{sumcheck}}\leftarrow v_{\mathrm{batch}}$.
> 2. Both parties run the following rounds for $j=0,\ldots,k-1$:
>    1. Prover sends the coefficients of $g_j(X)$, with $\deg g_j\le3$.
>    2. Verifier requires $e\,(g_j(0)+g_j(1))=v_{\mathrm{sumcheck}}$.
>    3. Both parties absorb the coefficients into $T_{\mathrm{chunk}}$, then derive $z_{\mathrm{sumcheck},j}\in E$.
>    4. Both parties update:
>
>       $$
>       \begin{aligned}
>       v_{\mathrm{sumcheck}} &\leftarrow g_j(z_{\mathrm{sumcheck},j}) \\
>       e &\leftarrow (1-z_{\mathrm{sumcheck},j})(1-z_{\mathrm{gkr},j})+z_{\mathrm{sumcheck},j}z_{\mathrm{gkr},j}
>       \end{aligned}
>       $$
>
> 3. Both parties return $(\mathbf{z}_{\mathrm{sumcheck}},v_{\mathrm{sumcheck}},e,T_{\mathrm{chunk}})$.
>
> Honest $g_j(X)=\mathrm{eq}(z_{\mathrm{gkr},j},X)\sum_{\mathbf{x}'\in\{0,1\}^{k-j-1}}\mathrm{eq}(\mathbf{z}_{\mathrm{gkr},>j},\mathbf{x}')G(\mathbf{z}_{\mathrm{sumcheck},<j},X,\mathbf{x}')$. The residual claim is $v_{\mathrm{sumcheck}}=e\,G(\mathbf{z}_{\mathrm{sumcheck}})$, where $e$ is the final coordinate's EQ factor (or $1$ if $k=0$); the caller checks it using the input evaluations.
>
> **Soundness — Sumcheck and EQ factoring (adapted).** Assume $\mathbf{z}_{\mathrm{gkr}}$ and the polynomial $G$ are fixed before this call's challenges, $G$ has individual degree at most two, and every round polynomial is fixed before its evaluation challenge. For a false incoming claim and a nonzero carried EQ factor $e$, the endpoint check forces the sent cubic to differ from the honest round polynomial. That discrepancy vanishes at $z_{\mathrm{sumcheck},j}$ with probability at most $3\mu$. The new EQ factor is $1-z_{\mathrm{gkr},j}+(2z_{\mathrm{gkr},j}-1)z_{\mathrm{sumcheck},j}$: it is $1/2$ if $z_{\mathrm{gkr},j}=1/2$, and otherwise vanishes with probability at most $\mu$.
>
> Charging each potentially vanishing factor as an exceptional event, a false incoming sum reduces to a false final claim $v_{\mathrm{sumcheck}}=eG(\mathbf{z}_{\mathrm{sumcheck}})$ except with probability at most $\min(1,(3k+Z)\mu)$, where $Z\le k$. Algorithm 4 receives the input evaluations and checks the final gate evaluation against this residual claim; its auxiliary checks and layer-reduction premises remain necessary. Algorithm 4 counts this reduction error once in its layer budget.

---

> **Algorithm 6 — OutputChecks: memory products and LogUp**
>
> **Input:** original sixteen-entry tables. **Output:** main read/write products $(\mathrm{RS}_{\mathrm{chunk}},\mathrm{WS}_{\mathrm{chunk}})$ and, for unified instruction circuits, the additional IT products $(\mathrm{RS}_{\mathrm{IT}},\mathrm{WS}_{\mathrm{IT}})$, after checking the lookup identities. Standalone IT returns its initialization/teardown products as the main pair.
>
> **Notation:** $Q$ is the query multiset and $T$ the lookup table; $m_t$ is table tuple $t$'s committed multiplicity. Tuples have width $w$, including any table identifier. With lookup challenges $\alpha,\beta$, define $\ell(t)=\beta+\sum_{j=0}^{w-1}\alpha^j t_j$.
>
> 1. For each main or additional IT product pair $(A_R,A_W)$, compute:
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
> This sum covers all categories sharing $\alpha,\beta$. Fewer than $p$ query occurrences per category suffices for the nonzero-count premise; the actual per-circuit query bounds and numerator degrees remain to be established. The returned memory products are exact products of the authenticated output entries; Algorithm 9 tests their global equality. Compression-tree verification is charged to Algorithm 4.

---

> **Algorithm 7 — WHIR**
>
> **Input:** cap groups $(\mathtt{MemoryCaps},\mathtt{WitnessCaps},\mathtt{SetupCaps})$; opening claim $(\zeta,\mathbf{a})$, with $f_j(\zeta)=a_j$; $\gamma$; the chunk transcript $T$ continued after GKR and batching. **Parameters:** oracle layout, domains, fold/query schedule and PoW thresholds from Algorithm 12. **Prover data:** base and folded polynomials and Merkle trees. **Relation:** the committed base polynomials have the claimed evaluations and required encoding/degree bounds. **Output:** acceptance of the base-opening claims and the updated transcript $T$.
>
> **Notation:** $f_j$ are the committed multilinear polynomials and $\zeta$ their opening point. For monomial coefficients $c_t$, $F_f(X)=\sum_t c_tX^t$ and $\mathrm{powers}(s)=(s,s^2,s^4,\ldots)$, so $F_f(s)=f(\mathrm{powers}(s))$; low-index bits select the first folded variables. $\mathrm{eq}$ is the interpolation kernel from EQSumcheck; $w$ is the running weight function, $m$ the remaining dimension and $D_r$ the current Reed–Solomon evaluation domain.
>
> **Query sampling:** for $t$ indices of $\ell_{\mathrm{query}}=\log_2(|D_r|/2^{k_r})$ bits each, draw $8\lceil(\lceil t\ell_{\mathrm{query}}/32\rceil+1)/8\rceil$ raw 32-bit words. For BabyBear, this stream begins with the checked PoW word. For Proth120, it begins with the next Keccak256 hash after the PoW digest, with each digest split into eight little-endian words. Skip the first word of this stream and read $\ell_{\mathrm{query}}$ bits per index, least-significant bit first. All drawn blocks advance the transcript; subsequent field challenges use fresh hash output.
>
> 1. Prover batches $f$; Verifier initializes $v,w$:
>
>    $$
>    \begin{aligned}
>    f &\leftarrow \sum_j\gamma^j f_j \\
>    v &\leftarrow \sum_j\gamma^j a_j \\
>    w(x) &\leftarrow \mathrm{eq}(\zeta,x)
>    \end{aligned}
>    $$
>
>    Maintain $v=\sum_{x\in\{0,1\}^m}f(x)w(x)$. The current oracle is the committed base polynomials in memory/witness/setup order, with packing groups specified in Algorithm 12.
> 2. For each nonfinal round $r$:
>    1. For $j=0,\ldots,k_r-1$, set $(a_j,f,v,w,T)\leftarrow\mathrm{QuadraticStep}(f,v,w,T)$ (Algorithm 8), with $f$ held only by Prover. Collect the fold challenges as $a=(a_0,\ldots,a_{k_r-1})$.
>    2. Prover sets $f_{\mathrm{next}}\leftarrow f$ and sends a cap committing to it. Both parties absorb the cap into $T$ and draw $\xi$.
>    3. Prover sends $u$, claimed as $F_{\mathrm{next}}(\xi)$; both parties absorb $u$ into $T$. Prover sends the 64-bit query-PoW nonce. Both parties absorb it into $T$ and draw one 32-bit PoW word (256-bit for Proth120). Verifier requires $b_r$ leading zero bits. Both parties draw query indices $I_0,\ldots,I_{t_r-1}$ using the query-sampling rule above, then derive $\delta$ from fresh hash output beyond the query-index randomness.
>    4. For each query $j=0,\ldots,t_r-1$:
>       1. Prover sends current-oracle leaves and Merkle paths.
>       2. Verifier authenticates each leaf against its cap at the configured tree position and runs Fold (Algorithm 8) with the selected encoding, challenges $a$ and query coset points. For base oracles, Verifier combines the per-polynomial folds with the same $\gamma$ powers used in step 1 to obtain $q_j$; later rounds fold the single batched oracle.
>       3. Set $s_j\leftarrow(\omega^{I_j})^{2^{k_r}}$, where $\omega$ generates the current oracle's domain.
>    5. Verifier updates:
>
>       $$
>       \begin{aligned}
>       w &\leftarrow w+\delta\,\mathrm{eq}(\mathrm{powers}(\xi),\cdot) \\
>         &\quad +\sum_{j=0}^{t_r-1}\delta^{j+2}\mathrm{eq}(\mathrm{powers}(s_j),\cdot) \\
>       v &\leftarrow v+\delta u+\sum_{j=0}^{t_r-1}\delta^{j+2}q_j
>       \end{aligned}
>       $$
>
>    6. Continue with $f\leftarrow f_{\mathrm{next}}$ and its commitment as the next round's oracle.
> 3. Final round:
>    1. For $j=0,\ldots,k_r-1$, set $(a_j,f,v,w,T)\leftarrow\mathrm{QuadraticStep}(f,v,w,T)$ (Algorithm 8), with $f$ held only by Prover. Collect the fold challenges as $a=(a_0,\ldots,a_{k_r-1})$.
>    2. Prover sends exactly $2^{N-\sum_r k_r}$ monomial coefficients $c$ of the remaining polynomial, where $N$ is the WHIR message dimension from Algorithm 12. Both parties absorb $c$ into $T$.
>    3. Prover sends the 64-bit final query-PoW nonce. Both parties absorb it into $T$ and draw one 32-bit PoW word (256-bit for Proth120). Verifier requires the final query-PoW threshold from Algorithm 12. Both parties draw the final query indices as in step 2.3.
>    4. Prover sends the current-oracle leaves and Merkle paths. Verifier authenticates the leaves and runs Fold, defining $s_j$ as in step 2.4. For each query require $q_j=\sum_l c_l s_j^l$.
>    5. Reconstruct $f_{\mathrm{final}}$ from $c$ and require:
>
>       $$
>       v=\sum_{x\in\{0,1\}^m}f_{\mathrm{final}}(x)w(x)
>       $$
>
> 4. Accept the base-opening claims and return $T$.
>
> The same fold challenges restrict $f,w$ and the authenticated leaves. The first round opens evaluation leaves from every nonempty base oracle: separate memory/witness/setup trees for ordinary or packed-delegation chunks, or merged memory/witness and separate setup trees for merged-feeder chunks or the terminal wrapper. Both layouts batch the committed polynomials in the same memory/witness/setup order with the claims' $\gamma$ powers; later rounds open coefficient leaves from the preceding fold commitment (Algorithm 8). Merkle paths are checked but not absorbed. Query evaluations constrain $f_{\mathrm{next}}$. For $m$ remaining variables, $\deg(F_f)<2^m$; the schedule fixes Reed–Solomon domains and expansion factors.
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
>
> **Memory-table binding export (proof obligation).** Algorithms 2 and 3b require the memory caps, together with the fixed circuit layout, to bind the memory columns before the shared $\mathbf r_{\mathrm{mem}}$ is sampled. Outside the accounted commitment/PCS failures, accepted openings and local chunk relations must refer to those same columns. This must cover adversarial caps as well as honestly encoded tables, both the ordinary memory commitment and the memory-column projection of the merged memory/witness commitment. The guarantee must hold at the memory-precommitment stage, before the later GKR, batching and WHIR challenges.
>
> **TODO — justify this export:** combine Merkle authentication, Algorithm 8's encoding correspondence and the proximity/candidate-list invariant to identify the column tables consistent with accepted proofs, specifying when those tables or candidate lists are fixed. If the result supplies a list rather than one fixed table, bound its size and account for any selection after the memory challenges in Algorithms 2 and 9; the single-table fingerprint bound cannot be imported unchanged. Carry these losses through the existing commitment/PCS and memory accounting, charging each failure once. This export and its numerical loss remain unproved.


---

> **Algorithm 8 — QuadraticStep and Fold**
>
> **Notation:** $a=(a_0,\ldots,a_{k-1})$ are fold challenges; $c_b$ are authenticated local monomial coefficients. $x$ is a nonzero coset point; $F_f$ is the univariate encoding of $f$. The $\kappa$ values are weights of restricted EQ terms.
>
> **QuadraticStep**
>
> **Input:** running claim $v$, weights $w$ and transcript $T$; Prover holds the current polynomial $f$. **Output:** fold challenge $a$, restricted polynomial $f$ and weights $w$, updated claim $v$ and transcript $T$. The polynomial $f$ is Prover-only input and output.
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
> 4. Return $(a,f,v,w,T)$.
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
> **Soundness — memory fingerprint (conditional).** Assume Algorithm 2 fixes $R,W$, including the boundary events, before the shared challenges are sampled, and the event encoding is injective on accepted data. If $R\ne W$, unique factorization makes the difference of their products nonzero: each affine factor has $r_{\mathrm{mem},\eta}$-coefficient 1, fixing its normalization. This difference has total degree at most $N=\max(|R|,|W|)$, so acceptance of unequal multisets has probability $\varepsilon_{\mathrm{mem}}\le\min(1,N\mu)$. Algorithm 1a charges this error once per statement, using a capacity bound that includes all instruction, delegation, IT and boundary events. Accepted-boundary injectivity, particularly for timestamp limbs reduced modulo $p$, remains a proof obligation. The reconstruction argument below supplies the execution interpretation of multiset equality.
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
> **Notation:** $x_j$ and $\mathrm{pc}$ come from $\mathrm{fin}$; `Hash` uses seven-round BLAKE2s with messages absorbed as raw 32-bit words.
>
> 1. Set $y\leftarrow(x_{10},\ldots,x_{17})$ and:
>
>    $$
>    e\leftarrow\mathrm{Hash}\bigl((\mathrm{pc},0^{15})\mathbin{\|}\mathtt{ProgramSetupCaps}\bigr)
>    $$
>
>    After PC, `Hash` zero-pads to fill the current input block (15 words), then absorbs the ordered setup caps. Timestamps are excluded.
> 2. **Base mode:** require $(x_{18},\ldots,x_{25})=0^8$; set $h\leftarrow\mathrm{Hash}(0^8\mathbin{\|}e)$.
> 3. **Otherwise, continuation mode:**
>    1. Set $h_{\mathrm{in}}\leftarrow(x_{18},\ldots,x_{25})$.
>    2. Prover sends the 16-word hash-chain preimage $(h_{\mathrm{prev}},e_{\mathrm{prev}})$, eight 32-bit words each. Verifier requires $\mathrm{Hash}(h_{\mathrm{prev}}\mathbin{\|}e_{\mathrm{prev}})=h_{\mathrm{in}}$.
>    3. **If $e_{\mathrm{prev}}=e$:** set $h\leftarrow h_{\mathrm{in}}$.
>    4. **Otherwise:** set $h\leftarrow\mathrm{Hash}(h_{\mathrm{in}}\mathbin{\|}e)$.
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
>    1. Verify the last proof:
>       - **BabyBear:** run `FullStatement`, obtaining $(y,h)$.
>       - **L1 wrapping:** produce a unified continuation proof with merged-feeder commitments, then prove that feeder Verifier's execution with the fixed terminal-wrapper parameters. Run `TerminalStatement` (Algorithm 1b), obtaining $(y,h)$. Require the proof's window identifiers to match those fixed for the terminal Verifier.
>    2. Require the last proof's setup caps (`ProgramSetupCaps` for BabyBear, `SetupCaps` for L1 wrapping) and final PC to match the expected setup caps and successful ending PC, and require $h=h_{\mathrm{expected}}$.
>    3. Accept and expose $y$ only if all verification and expectation checks pass; otherwise reject.
>
> Expected identities and $h_{\mathrm{expected}}$ are determined by the application starting values and selected recursive configuration. For L1, the EVM Verifier checks the expected final PC and window identifiers. It reports $y$ and $h$ as little-endian 32-bit register words concatenated in register order, and the setup identity as Keccak256 of the ordered setup-cap digests, with each digest's 32-bit words encoded big-endian. The application or registry must compare the reported setup identity and history with the expected values in step 4.2.
>
> **Soundness — recursive composition (conditional).** Assume Algorithm 1a's execution guarantee for every invoked configuration; binding and canonical interpretation of the history from Algorithm 10; and correctness of each selected Verifier program, including its child-input parsing, acceptance branch and transfer of $(y,h)$ to the designated registers. Expected setup identities, successful PCs and history must be fixed by the public claim. A recursive composition reduction must justify applying the component soundness bounds to child proofs carried inside execution witnesses, within an external bound $d$ on all proved invocations and their query/work budgets.
>
> Outside the corresponding failure events, terminal acceptance identifies a successful execution of the expected outer Verifier. Its verified local semantics imply child acceptance with the same result and the authenticated child history. Applying this implication at each handoff reaches the base application execution, so the exposed $y$ is its result. The algebraic error is bounded by the sum over all proved invocations; Algorithm 10 accounts for history binding, and terminal comparisons anchor the claimed identities and endpoints. Establishing the recursive reduction and each implementation handoff remains a proof obligation. Extending this argument to the stated L1 route additionally requires soundness of its terminal proof system and correctness of its serialization, public-claim mapping and contract linkage.

---

**Circuit and memory parameters for base/continuation FullStatement.** Merkle caps contain sixteen 256-bit hashes. $\mathrm{profile}$ and $\mathrm{mode}$ fix the instruction-family selection in Algorithm 12; the families have the following row counts and capacity charges.

- **Unrolled instructions:** add/sub/LUI/AUIPC/MOP (family 1); jump/branch/compare (2); shift/binary (3); unsigned multiply/divide (4); word memory (16); subword memory (17). Trace logarithms are 24 except multiply/divide, which uses 23.
- **Delegations:** BLAKE2s, bigint, Keccak special5, theta/rho, column parity and chi5, with trace logarithms $(20,22,22,22,22,22)$ and memory/permutation-argument terms per chunk $A_d=(44\cdot2^{20},20\cdot2^{22},15\cdot2^{22},17\cdot2^{22},15\cdot2^{22},13\cdot2^{22})$ in that order.
- **IT windows:** standalone IT has $2^{24}$ rows and eight windows of $2^{24}$ 32-bit words per proof. Unified has two windows of $2^{25}$ bytes per chunk. With identifiers below 64, unified covers windows below $2^{31}$ bytes; unrolled covers the $2^{32}$-byte range.
- **Unified capacity:** each circuit has $2^{23}$ rows but is charged $2^{24}$ cycles by the participant bound.

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
>    Use $\ell_{\mathrm{lookup}}$ for the lookup-PoW threshold in Algorithm 3a, step 4, and $\max(20,\ell_{\mathrm{lookup}})$ for the combined memory/lookup-PoW threshold in Algorithm 1b, step 3.
>
> 6. Return the ordered instruction-family list where applicable, and the selected field, transcript, commitment layout, column-packing factor, schedules, sizes and PoW thresholds.
>
> **Packed-delegation fixture.** The packed-delegation fixture uses the following fixed parameters for standalone chunk proving and verification: the [blake2_with_extended_control circuit](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json), BabyBear, shared memory challenges, $n=20$, $\mathrm{pack}=16$ and the packed-delegation row below. Its commitment layout and derived parameters follow steps 3–5. Before drawing the packing coordinates, both parties hash $T_{\mathrm{chunk}}$'s current seed once with seven-round BLAKE2s.
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
> | Merged-feeder | 23 | (1,5,5,5,4) | (16,32,1024,32768,1048576) | (21,17,9,5,4) | (29,26,25,26,21) |
> | Packed-delegation | 20 | (1,5,5,5,4,3) | (2,16,512,16384,524288,524288) | (89,23,10,7,5,5) | (26,24,25,19,21,21) |
> | Terminal wrapper | 22 | (2,4,4,4,4,4) | $(2^5,2^7,2^{11},2^{15},2^{19},2^{23})$ | (17,12,8,6,5,4) | (30,30,27,25,21,24) |
>
> Packed-delegation sources: [packed fixture configuration](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/verifier_common/src/test_circuits.rs#L175), [proving fixture](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/prover/src/tests/gkr/family_circuits.rs#L92), [packed parameter constructor](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/prover/src/gkr/prover_config/example_configs.rs#L206), [Verifier fixture](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/verifier_generator/tests/packed_verify.rs#L20).
>
> Terminal sources: [terminal parameter configuration](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/prover/src/gkr/prover_config/example_configs.rs#L227), [terminal prover selection](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/program_prover/src/l1.rs#L77), [Keccak Merkle hashing](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/prover/src/merkle_trees/keccak256_for_everything_tree.rs#L1), [operation modes](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/prover/src/gkr/prover/mod.rs#L72), [standalone transcript seed](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/verifier_evm/src/seed.rs#L22), [Proth120 field](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/field/src/proth120.rs#L4), [Keccak transcript](https://github.com/matter-labs/zksync-airbender/blob/c1a662222cafcd96db4383dce737edb79fa62b09/transcript/src/keccak256.rs#L64).

**Soundness — parameter instantiation (conditional).** Algorithm 12 fixes the circuit and commitment layout, field domains and challenge/query schedule to which the preceding bounds apply. For each selected circuit, instantiate Algorithm 4's batching/round/test counts, Algorithm 6's occurrence and numerator-degree bounds, and Algorithm 7's proximity/list and agreement bounds. The lookup charge $D_{\mathrm{lookup}}$ must dominate the degree sum actually proved in Algorithm 6. The PoW thresholds enter the computational accounting of the protected tests; their instantiation must use the challenge-distribution bound $\mu$ and the corresponding algebraic degrees. In particular, the BabyBear value $F=123$ in step 5 must be reconciled with $-\log_2\mu\approx121.66$ for the stated sampling rule. These per-configuration checks remain proof obligations.

For unrolled memory, let $n_f$ count chunks of instruction family $f$, let $2^{\ell_f}$ be its trace rows per chunk, and let $n_d$ count chunks of delegation type $d$. Let $A_d$ be that delegation type's per-chunk term count listed above, and let $n_{\mathrm{IT}}$ count standalone IT chunks. If Algorithm 2's charges bound all selected instruction/delegation events and each IT proof contributes at most $8\cdot2^{24}$ events on each side, then

$$
\begin{aligned}
N &\le 4\sum_f n_f2^{\ell_f} + \sum_d n_dA_d + 8n_{\mathrm{IT}}2^{24} + 33 \\
  &\le (2^{40}-1) + 2^{30} + 33 \\
\varepsilon_{\mathrm{mem}} &\le N\mu < 2^{-81.65}.
\end{aligned}
$$

The 33 boundary events are the ordinary registers and PC. This bounds the memory-fingerprint error in the algebraic model. The unified profile requires a separate event-count bound including its authenticated IT products.

**Composed error (conditional).** In the fresh-word algebraic model, assume the binding, encoding, reconstruction and recursive-composition premises above. For each statement, use Algorithm 3b's chunk bound and Algorithm 9's memory bound. For an externally bounded collection of at most $d$ proved invocations,

$$
\begin{aligned}
\varepsilon_{\mathrm{stmt}} &\le \varepsilon_{\mathrm{mem}} + \sum_{\mathrm{chunks}}(\varepsilon_{\mathrm{lookup}} + \varepsilon_{\mathrm{GKR}} + \varepsilon_{\mathrm{PCS}}) \\
\varepsilon_{\mathrm{alg,total}} &\le \min\!\left(1,\sum_{\ell=1}^d \varepsilon_{\mathrm{stmt},\ell}\right).
\end{aligned}
$$

Each bound must hold under the preceding transcript and permitted adaptive choices, with sums bounded over the allowed participant collections. Algorithm 10's $\varepsilon_{\mathrm{chain}}$ accounts for history-binding failures in the computational analysis. Algorithm 11's terminal comparisons and handoff conditions are deterministic premises; any additional terminal proof system contributes its own soundness term.

**Fiat–Shamir security.** The bounds above give conditional algebraic soundness guarantees under fresh transcript randomness, including field-sampling bias and the stated per-candidate PoW bounds. Let $q$ bound the adversary's total random-oracle queries across all transcript and nonce trials. A complete Fiat–Shamir proof must establish round-by-round soundness for the composed protocol and derive its computational soundness bound as a function of $q$, accounting for adaptive trials, repeated oracle inputs and commitment binding. The main unresolved obligations are WHIR's proximity/list-decoding invariant and the memory participant-binding, event-encoding and execution-reconstruction lemmas. Recursive composition additionally requires the handoff guarantees stated in Algorithm 11.

---

**References:** [GKR](https://people.cs.georgetown.edu/jthaler/GKRNote.pdf), [LogUp](https://eprint.iacr.org/2022/1530), [GKR lookup compression](https://eprint.iacr.org/2023/1284), [WHIR](https://eprint.iacr.org/2024/1586), [Two Shuffles Make a RAM](https://eprint.iacr.org/2023/1115).

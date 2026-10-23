## 4bis. small extras on proof end

### Base proof and unrolled continuation

_Describe the base full-statement verifier, the proof data passed to it, and the
unrolled recursive continuation layers._

- make  sure to mention the special modes of unpacking inputs in the chain

- <mark><strong>Recursive Layer Outputs</strong> are sixteen words returned by a full-statement verifier program: eight application-result words and eight recursion-chain words. The next layer proves that program's execution, including verification of the supplied inner proof. Acceptance binds the execution to the intended verifier program and its successful termination point. The base layer initializes the chain; continuation layers authenticate and propagate the inner result and chain.</mark>

- <mark><strong>Recursion History</strong> uses the configured hash variant to derive an end-parameter digest E from the final PC, padded to sixteen words, followed by the ordered setup commitments. The base chain is H(0^8 ‖ E). A continuation authenticates a supplied preimage against the incoming chain hash, preserving that hash when the latest E equals the current end-parameter digest, or updating it to H(previous_hash ‖ E) otherwise. Terminal acceptance checks the chain against the intended application and verifier sequence. Consecutive repetitions are compressed, so the chain does not count recursion depth.</mark>

### Unrolled-to-unified bridge

_Describe what changes at the bridge, what inner statement remains the same, and
which values bind the two recursion modes._

### Unified continuation

_Describe repeated unified recursive verification and its stopping condition._

### Terminal verification and external acceptance

_Describe the final proof shape, public claim, optional L1 path, verifier identities,
and the condition under which an external consumer accepts the result._
aims._

## 6. Soundness and assumptions

### End-to-end soundness goal

_State the intended consequence of final-proof acceptance and the knowledge or
existence claim made about a complete program execution._

### Algebraic and cryptographic assumptions

_List the field, hash, Fiat-Shamir, polynomial-commitment, and extraction assumptions
on which the claim depends._

### Baseline constructions

_Identify the standard or clean baseline for GKR/Sumcheck, WHIR, lookups, memory
consistency, batching, and recursion._

<u>DO NOT FORGET TO ADD PAPER REFERENCES FOR EVERY FORMULA</u>

- **Schwartz-Zippel Soundness Lemma**

- **RLC Fingerprinting**
  - follows from above
  - why it is reasonable to use this everywhere we want compression or random evaluation as a fingerprint identifier

- **Security-Bits Soundness Gain**
  - 100 bits
  - connected to Fiat-Shamir of course otherwise 100 bits make no sense

- **(Extension) Field Soundness Gain**
  - downstream from 31-bits
  - also L1 base 128ish-bits

- **Fiat-Shamir (Non-Determinism) Soundness Loss**

- **Sumcheck Soundness Loss**

- **Batched Sumcheck Soundness Loss**

- **GKR Soundness Loss**
  - layers, constraints

- **LogUp Soundness Loss**

- **Memory Soundness Loss**

- **Merkle-Tree Soundness Loss**

- <mark><strong>Shared Memory Challenges</strong> are derived from the whole-execution transcript, binding final-state data and the ordered participating memory commitments and their context. Every chunk uses these external challenges, and the full-statement Verifier reconstructs their derivation and checks equality. Lookup challenges are instead sampled separately within each chunk after its setup, memory, and witness commitments, including multiplicity columns. The chunk transcript also binds the supplied external memory challenges.</mark>

_Then comes the Verifier PCS Schedule Section_

- **Proxmity Theorems**
  - $\delta$ distance
  - $\lambda$ security bits
  - $PoW$ grinding bits
  - $LDE = 1/\rho$
  - $\epsilon_t \le (1 - \delta)^t$ from WHIR paper
    - $\epsilon_\lambda = 2^{- \lambda} \ge \epsilon_t \implies t \ge \lceil \lambda / -log_2(1 - \delta) \rceil$
  - $\epsilon_{PoW} \le 2^{- PoW}$ from S-Two paper
    - $\epsilon_\lambda = 2^{- \lambda} \ge \epsilon_{PoW} \cdot \epsilon_t \implies t \ge \lceil (\lambda - PoW) / -log_2(1 - \delta) \rceil \textit{ when } \lambda \ge PoW\ bits$
  - Unique Decoding $\delta_{uniq} = (1 - \rho) / 2$
    - $t_{uniq} \ge \lceil (\lambda - PoW) / -log_2(\frac{1 + \rho}{2}) \rceil$
  - Johnson List Decoding $\delta_{John} = 1 - \sqrt\rho$
    - $t_{John} \ge \lceil 2 (\lambda - PoW) / log_2(LDE) \rceil$
  - Broken Capacity Conjecture $\delta_{cap} = 1 - \rho - \epsilon,\ \epsilon \gt 0$ from Proximity Gaps paper and WHIR paper
    - $t_{cap} \ge \lceil (\lambda - PoW) / -log_2(\rho + \epsilon) \rceil \ge \lceil (\lambda - PoW) / log_2(LDE)\rceil \ when\ \epsilon \approx 0$
    - Broken by .. paper
  - Airbender 20% Pessimistic Capacity Conjecture
    - $t_{Air} = \lceil 1.2 \cdot t_{cap} \rceil \ge \lceil 1.2 (\lambda - PoW)/log_2(LDE) \rceil$
> 1. Code rate and distance. Define ρ=k/n=1/B, where k is the polynomial coefficient count, n the encoded evaluation count, and B the LDE expansion factor. Relative Hamming distance δ measures the fraction of positions at which two words disagree.
> 2. Why list decoding enters. Beyond the unique-decoding radius, a committed word may be close to several valid polynomial encodings. The analysis must bound that candidate list and control what happens under random combinations and folds—this is where list-size bounds and mutual correlated agreement matter. The verifier does not actually run a list-decoding algorithm
> https://people.csail.mit.edu/dmoshkov/courses/codes/listdecoding-NOW.pdf

- **LDE-Ratio (STIR) Soundness Gain**

- **PCS-Query Soundness Gain**
  - try ethproofs Soundness calculator

- **List-decoding (Johnson to Conjecture) Soundness Loss**
  - recent conjectures
  - small-prime-field issues
  - 20% safety margin

- **PCS-OOD Soundness Gain+Loss**

- **WHIR (OOD, etc) Soundness Loss**
  - mention grinding before every non-ood query round
  - ε_comb poly batching
  - ε_OOD list identification
  - ε_queries query agreement (varies by round)
  - ε_shift query batching
  - ε_binding merkle trees
  - ε_folding sumcheck round
  - conditional analysis, by piling up Pr[next step repairs that invalidity] ≤ ε_step 
    - round → fixed transcript data → invalid-state condition → failure formula → assumptions → grinding → numerical bound

- **Batched (DEEP) WHIR Soundness Loss**
  - mention grinding for the batch because the number of queries is reduced
  - a rather complicated computation of errors here, binding together RLC batching for compression, MCA for proximity, LIST for combinations, QUERY for RLC consistency.
ε_total ≤ ε_comb + ε_queries + ε_folding + ε_OOD + ε_binding. Most of it from WHIR paper (collection of other results)

- **Grinding (PoW) Soundness Gain** is a technique whereby a small amount of completeness loss is exchanged for a large amount of soundness gain. Before drawing a specific batch of challenges, the Prover performs a search approximately $2^{PoW+\epsilon}$ values to find a $(PoW+\epsilon)$-bit nonce which once appended to the Fiat-Shamir transcript will yield a hash output with $PoW$ leading bits set to zero. The Verifier then proceeds with drawing from the transcript, validating and discarding these leading bits. The technique significantly restricts the number of theoretically valid transcript combinations, however it also exponentially aguments soundness by boosting challenge querying security bits by as many bits as are required to be leading zeros. When the Prover has access to a parallel computational accelerator, such "grinding" searches yield a minimal impact on Prover runtime for a significant security boost. This technique is used by Airbender to keep total PCS query count low (ie low proof size) and nevertheless maintaining a high level of overall security guarantee.

- **PCS-Fold Soundness Loss**
  - already covered by LDE-Ratio?

- **Recursion Soundness Loss**
  - ???

- **Lean References**
  - if possible, connect to existing public Lean definitiosn

- **Soundness Extractability**
  - if possible, W3 goal

### Airbender production deviations

_Enumerate every soundness-relevant difference between those baselines and the
production protocol, omitting purely operational optimizations._

### Local proof-system errors

_Account for GKR/Sumcheck, WHIR, lookup, range-check, memory-fingerprint, batching,
and other algebraic error terms._

### Challenge causality and reuse

_State which values are bound before each challenge, where challenges are reused,
and why prover-controlled data cannot adapt to them._

### Composition across chunks and recursion

_Explain how individual chunk claims, the full-statement verifier, recursive layers,
and terminal verification compose without omissions or duplicated execution._

### Concrete security parameters

_Record the selected fields, extension degrees, query counts, fold schedules,
grinding, hash modes, and other parameters needed for a concrete bound._

### Total error bound

_Combine invocation multiplicities and component errors into the claimed end-to-end
soundness bound without double-counting shared challenges._

### Remaining proof obligations

_List the standard, adapted, and new lemmas or implementation-binding arguments that
must still be completed for the W2 or W3 deliverable._

### Open questions

_Keep unresolved semantic decisions and disputed implementation interpretations here
until they are reviewed. Do not silently turn them into accepted specification
cl
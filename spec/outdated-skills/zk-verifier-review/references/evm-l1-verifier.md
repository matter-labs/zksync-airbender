# Solidity/Yul and EVM/L1 Verifier Review

## Contents

1. Security boundary
2. Applicability and current Airbender snapshot
3. Classify what the L1 verifier actually verifies
4. Recover the on-chain accepted statement
5. Generator-to-deployment provenance
6. Byte-accurate calldata parsing
7. Field, integer, and encoding semantics
8. Fiat-Shamir and cross-language relationship/parity
9. Split GKR/WHIR verification and handoff commitments
10. Single-chunk versus global memory closure
11. Recursive-chain closure
12. Contract-to-contract authentication
13. Public outputs and state-transition authorization
14. Yul memory, stack spilling, and compiler behavior
15. EVM arithmetic and control flow
16. Merkle, WHIR, and grinding details
17. Gas, code size, and liveness
18. Differential and adversarial testing
19. Audit artifacts
20. Checklist and primary sources

## Scope proportionality

This chapter is intentionally deep because an on-chain acceptance boundary can
invalidate an otherwise sound native verifier. Load it only when Solidity/Yul,
generated EVM artifacts, recursive settlement, or a deployed L1 caller is in
scope. First use §§1–5 to establish whether the path is authoritative and
deployed. If it is only an unused prototype, record that coverage boundary and
do not spend a Rust-only focused review auditing every Yul optimization. If it
is the final acceptance boundary, §§6–20 are not optional.

## 1. Security boundary

The L1 verifier is the final acceptance boundary. Its security statement is not
merely:

```text
some Solidity/Yul execution did not revert
```

It is:

```text
the exact deployed verifier, under the exact deployed wrapper and configuration,
accepted the exact final recursive statement that the settlement/state-transition
contract intended, and only that authenticated acceptance authorized the L1 effect
```

Audit all of these as one predicate:

```text
AcceptL1(
    chain and deployment context,
    expected program/setup/version/security configuration,
    expected recursion-chain terminus,
    expected public input/output or state-transition commitment,
    calldata proof,
    deployed verifier bytecode and helper contracts
) -> authorized state transition
```

The first principle still applies: every calldata byte, transaction ordering
choice, registry write, caller-controlled address, and returned word is adversarial
until pinned. The additional EVM rule is:

**A successful external call is not an authenticated verification result unless
the caller proves it invoked the intended code, checks the success/revert result,
validates any required return data, and consumes a statement-bound result.**

Do not treat gas optimization, Solidity/Yul generation, registry linkage, proxy
routing, or transaction splitting as deployment details outside the proof system.
Each can change the language accepted on L1.

## 2. Applicability and current Airbender snapshot

This section describes repository commit
`e072ba30a3b738375b0cc9cc1b04767065d2a52d` as inspected on 2026-08-14. It is a
versioned search profile, not a claim about a later production deployment.

Relevant surfaces include:

- `verifier_evm/ARCHITECTURE.md`: intended machine, chunk, global-argument, and
  recursion-chain model;
- `verifier_evm/src/generator/`: circuit/config-to-Solidity generation;
- `verifier_evm/src/templates/gkr.sol`: hand-written GKR/Yul verifier template;
- `verifier_evm/src/templates/whir.sol`: hand-written WHIR/Yul verifier template;
- `verifier_evm/src/templates/GkrWhirRegistry.sol`: two-transaction linkage;
- `verifier_evm/src/flatten.rs`: Rust proof-to-calldata encoding;
- `verifier_evm/src/seed.rs`: initial and handoff-seed reconstruction helpers;
- `verifier_evm/generated_contracts/`: generated sources, compiler settings, and
  two-transaction integration test;
- `full_statement_verifier/src/unified_circuit_statement.rs`: native unified
  full-statement and recursive-chain semantics to which the final proof should
  correspond;
- `full_statement_verifier/src/recursion_chain.rs`: host-side chain construction.

At this snapshot, `generate_verifiers` emits three contracts for a Proth120,
Keccak-based proof:

```text
circuit artifact + prover WHIR schedule + packing/PoW/final-PC parameters
  -> generated GKR verifier
  -> generated WHIR verifier
  -> GKR/WHIR registry
```

The proof is split across two transactions. Each verifier computes a commitment
to the GKR-to-WHIR handoff state and interacts with a registry key. Re-derive,
from the target checkout and deployed caller, the complete checks performed by
each half, who may mark the registry, whether marks can be replayed or overwritten,
whether external-call failure is rejected, and where the recursion chain is
finally anchored. These are investigation questions, not findings supplied by
the profile. Do not silently assume a missing wrapper or authorization layer
exists, and do not assume the template itself is the production acceptance
authority.

The current generated path is therefore not evidence that the intended final L1
design has been completed. Re-fingerprint the target commit, generated sources,
deployed addresses, bytecode hashes, compiler metadata, and settlement caller.

## 3. Classify what the L1 verifier actually verifies

Do not assume “one proof” means one base execution chunk. Resolve one of these
architectures explicitly:

| Architecture | What L1 sees | What must already be proved below L1 |
|---|---|---|
| Direct base-chunk verification | One ordinary execution chunk proof | Its complete local statement; no omitted cross-chunk obligations |
| Unified final-chunk verification | One proof of a unified verifier-program execution | The verifier program checked all supplied inner proofs and emitted a fully anchored recursive statement |
| Final recursive-proof verification | One outer proof whose witness contains an arbitrarily deep proof chain | Inductive correctness of every recursive link, base-case selection, chain termination, inner statement/key binding, and public-output propagation |
| Split protocol verification | GKR and PCS/WHIR halves in separate calls or transactions | A complete, authenticated, collision-resistant handoff state and atomic/equivalent final acceptance rule |
| Legacy STARK verification | One AIR/quotient/DEEP-FRI proof or its recursive wrapper | Trace/auxiliary/quotient commitments, OOD claims, FRI terminal data and queries, public statement, and recursive output follow the historical verifier schedule |

Airbender's intended L1 path may use a single unified circuit chunk because a
recursive verifier program is deliberately compressed to fit that shape. That
does **not** mean the original execution had one chunk, or that global memory was
never global. It means the recursive program should have already verified and
closed the inner whole-program statement. The L1 verifier must authenticate the
outer verifier program/setup and the recursive public outputs that carry that
closure.

If the outer program itself uses more than one unified chunk, local equality in
each per-chunk permutation argument is not automatically equivalent to the native
multi-chunk aggregation rule. Record the actual outer proof count and accumulator
ownership.

For a legacy Airbender STARK contract, retain every calldata, field-arithmetic,
transcript, deployment, call-authentication, and settlement check in this
reference, but substitute the AIR/quotient/DEEP-ALI/FRI round obligations from
`stark-deep-fri.md` for legacy AIR/STARK-specific ones.

## 4. Recover the on-chain accepted statement

Build an L1 statement table before reading hot-loop algebra:

| Statement component | Authoritative source | How contract receives it | How it is pinned | Settlement use |
|---|---|---|---|---|
| verifier/program identity | governance/deployment constant or immutable setup digest | compiled constant, immutable, storage, or calldata | code hash/setup-cap comparison | selects the verified program |
| protocol/version/security mode | deployment configuration | bytecode/constants | authenticated deployment/version tag | fixes soundness parameters |
| final PC / success condition | expected program metadata | compiled constant or trusted state | equality after proof binding | establishes successful termination |
| setup/verifier key | expected setup registry | cap/digest in proof or storage | equality/authenticated lookup | binds circuit and program |
| recursion-chain end | expected rollup/upgrade chain state | final registers/public output | equality to expected chain value | prevents wrong/truncated chain |
| base program output | rollup state-transition statement | final registers/public output | proof binding plus caller comparison | drives L1 state transition |
| final timestamp/cycle bound | protocol statement | proof/public value | transcript, memory closure, and range check | bounds execution and state closure |
| GKR/PCS handoff | verifier-derived state | registry key or direct call memory | complete commitment and authorized marks | joins proof halves |
| chain/deployment/session context | L1 state | storage/immutable/environment | explicit namespace or caller check where replay matters | prevents cross-context reuse |

For every item, decide whether it is:

- part of the proof-system statement and therefore must be bound into the
  transcript or authenticated setup;
- an L1 policy value checked after cryptographic verification;
- a deployment trust assumption;
- or an untrusted prover/caller choice.

It is valid for L1 policy values to be checked outside the Fiat-Shamir transcript
when the cryptographic proof exposes a collision-resistant, unambiguous public
output that the caller compares. It is not valid to compare a different copy,
unbound cache, event field, or overwriteable registry value.

## 5. Generator-to-deployment provenance

Construct this exact graph:

```text
circuit source and recursion verifier binary
  -> compiled GKR circuit artifact and setup caps
  -> prover configuration / WHIR schedule / security level
  -> verifier_evm generator inputs
  -> Solidity templates + emitted circuit Yul
  -> generated Solidity sources
  -> exact solc version, via-IR setting, optimizer details/runs, EVM target
  -> creation bytecode and runtime bytecode
  -> deployed address/code hash or proxy implementation
  -> registry/helper addresses
  -> settlement contract entrypoint and accepted return/storage/event
```

Audit:

- every generator argument, especially final PC, PoW bits, cap size, packing,
  trace width, round schedule, field, hash, and security level;
- whether generated sources are reproducible from the reviewed artifact/config;
- whether committed generated sources are stale;
- whether tests compile the same files and settings as deployment;
- `solc` versus alternative compiler/backend behavior;
- exact compiler release and all known bugs applicable to its code-generation
  path;
- optimizer and `viaIR` settings, since hand-written memory layout can interact
  with generated stack spilling;
- runtime bytecode size and whether a split-contract design changed the trust
  boundary to fit deployment limits;
- linked library/helper/registry addresses and whether they are immutable;
- proxy/admin/beacon behavior, initialization, upgrades, and storage collisions;
- chain-specific deployed code hash and EVM fork assumptions;
- constructor arguments, immutables, and post-deployment configuration;
- whether the state-transition caller verifies the designated deployment rather
  than accepting a caller-supplied verifier address.

Do not stop at source equivalence. Compare the deployed runtime bytecode and its
metadata/configuration with a reproducible build.

## 6. Byte-accurate calldata parsing

Yul fallback verifiers often use a custom packed stream rather than Solidity ABI
decoding. Build a byte ledger:

| Offset/range | Width | Meaning | Decode/endian | Domain check | Transcript action | Cursor after |
|---|---:|---|---|---|---|---:|

Track reads in executed order, including reads at computed offsets and tail reads.
For each `calldataload`, `calldatacopy`, `byte`, `shr`, `shl`, `and`, or pointer
increment, check:

- exact start offset and byte width;
- whether the read crosses a 32-byte word;
- big-endian word position and lane extraction;
- addition, multiplication, subtraction, and shift overflow;
- cursor update and branch-dependent consumption;
- whether the code checks `calldatasize()` before the value is used;
- whether an out-of-range load/copy can supply zero bytes and make a truncated
  proof look like explicit zeros;
- exact end-of-proof equality, not merely `cursor <= calldatasize()`;
- trailing bytes, trailing zeroes, and concatenated-proof ambiguity;
- `calldatasize() - tail_len` underflow on short calldata;
- accidental interpretation of the first four proof bytes as a function selector,
  or vice versa;
- fallback routing and whether arbitrary selectors or receive/value paths reach
  verification;
- fixed proof layout agreement with the Rust flattener for every supported circuit
  shape and schedule.

An end-cursor check is powerful but not sufficient. A value may already have been
used before the final check, and a wrapped offset can read a different location
while still allowing a plausible cursor. Prove every offset bound locally or from
fixed generated constants.

For current Airbender, record the mixed encodings rather than simplifying them:

- the initial GKR transcript preimage is a stream of little-endian `u32` words;
- field elements in later proof regions are 16-byte big-endian `u128` values;
- nonces are 8-byte big-endian values;
- Merkle digests/caps are raw 32-byte values, with conversion between the
  repository's `[u32; 8]` representation and on-chain byte order;
- pairs of field elements can share one 32-byte calldata word.

Mixed but fixed encoding is valid. It is also an unusually high-risk parity
boundary.

## 7. Field, integer, and encoding semantics

The EVM stack is 256-bit. The protocol fields and machine values are not.

### Canonical field elements

For every prover-supplied field lane determine whether the verifier:

1. rejects `x >= p`;
2. reduces `x mod p` before both transcript absorption and algebraic use; or
3. inconsistently hashes one representation and computes with another.

Option 1 gives canonical proof bytes. Option 2 can be algebraically sound when
every semantic and transcript use is of the reduced value, but makes proof
encoding malleable and must be intentional. Option 3 gives the prover extra
transcript freedom and is a soundness candidate.

Check every GKR coefficient, final evaluation, packed lane, WHIR coefficient,
OOD value, terminal coefficient, query leaf value, challenge, cached evaluation,
and public-output field. Do not infer consistency from one helper: generated
circuit code and hand-written templates may decode separately.

### Integer widths and dirty bits

For `u32`, `u64`, address, timestamp limb, count, bit index, and nonce values:

- reject unused high bits or prove they are completely ignored in hashing and use;
- distinguish `mask` from range validation;
- verify signed/unsigned comparisons and shifts;
- verify PC/timestamp word and limb order;
- verify timestamp reconstruction and maximum cycle bound against the exact
  circuit constants, not a remembered `2^32` limit;
- check `bool`/tag values are exactly in their intended set;
- check zero and maximum-width edge cases.

### Challenge mapping

Recompute the distribution induced by hash-word truncation and modular reduction.
For Proth120, check the exact 128-bit extraction, reduction, and exceptional values.
Bias, repeated draw semantics, and zero challenges must match the soundness budget.

## 8. Fiat-Shamir and cross-language relationship/parity

Reconstruct the EVM transcript from the contract alone, then compare with:

- Rust native verifier for the same proof configuration;
- Rust proof flattener;
- prover transcript only after the verifier schedule exists;
- generated circuit Yul;
- any recursive in-guest verifier;
- the split WHIR verifier and registry handoff.

Do not demand byte-for-byte equality between intentionally different proof-system
configurations. Current native recursive verification may use BabyBear and Blake2s,
while the on-chain outer proof uses Proth120 and Keccak. Demand equality of the
interactive protocol obligations and exact byte equality only for implementations
that claim to verify the same concrete proof.

At the profiled Airbender snapshot, the on-chain initial transcript is a concrete
different state machine:

- field: Proth120, serialized as 16-byte big-endian `u128` values after the
  initial word stream;
- hash: Keccak-256;
- initial preimage in the production Rust `seed.rs`: final register
  `(value, ts_low, ts_high)` words, final PC/timestamp words, teardown top bits,
  setup cap, and merged memory+witness cap, encoded as little-endian `u32`
  words;
- there is no separate witness cap or supplied flattened external-challenge
  tuple in that preimage because the commitment mode merges memory+witness and
  derives the external tuple here;
- the big-endian 8-byte nonce is folded into the seed unconditionally, including
  zero PoW difficulty, before checking the configured leading-zero threshold;
- nine challenges are drawn sequentially; each draw replaces the seed with
  `keccak256(seed)` and maps the first 16 digest bytes as a big-endian `u128`
  modulo Proth120; the first seven form six independent memory linearization
  challenges plus the additive challenge, and the last two are the lookup
  challenges;
- later field-element absorption uses canonical 16-byte big-endian values.

Re-derive this recipe from the target template and flattener. The repository's
`gkr_transcript_reference.md` may describe an older preimage layout; a passing
Rust mirror test is not evidence that the current generated Solidity or deployed
bytecode follows it.

For each challenge record:

```text
state before -> exact calldata bytes absorbed -> canonicalization -> hash call
-> selected digest bytes -> field mapping -> state mutation -> later uses
```

High-risk EVM-specific points:

- custom fixed-width encodings with no labels or lengths;
- a compiled circuit/version not included in the seed because the generator
  assumes its bytecode provides implicit domain separation;
- absorbing reduced field values while WHIR hashes raw bytes, or vice versa;
- zero-length or conditional hash inputs;
- overlapping `mstore` writes that retain dirty bytes in a Keccak preimage;
- hashing a memory range larger than the meaningful bytes;
- failing to include the prior seed when absorbing the next message;
- draw functions that do or do not advance state inconsistently;
- PoW nonce folding and post-PoW extra draw/skipped-word behavior;
- challenge reuse caused by a local `seed` shadow that is not written back;
- transcript state copied into calldata for a second transaction without a complete
  authenticated handoff;
- missing expected program/setup/public-output context.

Use golden challenge traces, but remember that matching honest traces proves
parity/completeness, not schedule soundness.

## 9. Split GKR/WHIR verification and handoff commitments

When GKR and PCS verification occur in separate calls or transactions, model the
handoff as a commitment scheme in its own right:

```text
GKR verifies claims
  -> derives complete PCS input state S
  -> C = H(domain || canonical_encode(S))
  -> authenticated mark_GKR(C, public statement/output)

WHIR receives S
  -> checks C = H(domain || canonical_encode(S))
  -> verifies PCS relation for exactly S
  -> authenticated mark_WHIR(C)

settlement accepts only the same C with both authenticated marks and the intended
public statement/output
```

Inventory every component of `S`. In the current template, the intended handoff
contains the post-GKR seed, WHIR batching challenge, batched opening value, complete
evaluation point, memory/witness cap, and setup cap. Verify:

- all GKR base claims are included exactly once in the batched opening;
- packing coordinates and base-layer coordinates are ordered identically;
- batching challenge and opening are canonical and tied to the GKR transcript;
- both base caps are complete, ordered, and byte-identical;
- the WHIR verifier uses every supplied handoff component in the claimed opening;
- the commitment is domain-separated from unrelated uses;
- the GKR mark also binds the exact public output and setup/program identity that
  settlement consumes;
- the registry cannot pair marks from unauthorized contracts or deployments;
- a mark cannot be overwritten with different public data for the same commitment;
- replay, stale partial marks, front-running, transaction reordering, and chain
  reorganization do not change the accepted statement;
- the final consumer checks the complete accept state, not merely an event or one
  bit;
- failed registry notification makes the verifier operation fail when linkage is
  required.

Hash equality is sufficient to join the halves only under collision resistance and
a canonical, complete preimage. It does not authenticate who asserted that either
half verified.

Prefer one atomic verification call where feasible. If gas/code-size constraints
require multiple transactions, make the persistent protocol an explicit state
machine with authenticated writers, immutable verifier identities, statement
namespacing, safe overwrite/idempotence rules, and an unambiguous consume/finalize
operation.

## 10. Single-chunk versus global memory closure

A final unified proof may legitimately make the memory argument “local” to one
outer chunk, but only after proving all required global closure inside that chunk's
statement.

For a genuine single outer chunk, require:

- all active cycles of the recursive verifier program fit the authenticated trace
  shape;
- padding is neutral for computation, memory, delegation, lookups, and state;
- final register values/timestamps and final PC/timestamp are included before
  external memory challenges;
- all memory and witness caps are committed before those challenges;
- read and write accumulators include every program tuple exactly once;
- verifier-owned initial machine state and public final machine state are injected;
- initialization/teardown behavior is integrated or separately proved exactly once;
- delegation/precompile calls are fulfilled and included;
- the final read/write product equality is enforced;
- timestamp capacity and cycle count are in range;
- setup/program identity is authenticated.

If there are two or more outer chunks, identify the aggregator that multiplies all
per-chunk accumulators under one external challenge tuple and closes equality only
after every contribution and injection. A per-contract check of each chunk in
isolation can be too strong for completeness or too weak for soundness depending on
how cross-chunk memory is represented.

The final recursive proof does not need L1 to replay the base execution's global
memory argument. It needs L1 to verify the exact recursive verifier program that
already performed that aggregation and to bind the output that attests to it.

## 11. Recursive-chain closure

Treat recursion as an inductive proof with three separately audited statements:

### Base case

- base-versus-recursion mode is fixed by the authenticated program/setup, not a
  prover tag;
- the base program's auxiliary chain registers have the required zero state;
- its public output is extracted from the correct registers/limbs;
- its successful final PC and setup/program cap form the intended `end_params`;
- the genesis chain value is derived with the exact hash, round count, word order,
  padding, and domain.

### Recursive step

- the outer verifier program verifies the complete inner proof statement;
- the inner setup/verifier key, proof type, security level, and public inputs are
  bound;
- the supplied previous-chain preimage hashes to the chain value carried in the
  verified machine registers;
- every word of the preimage and digest is checked;
- the current program's `end_params` binds final PC and setup/program identity;
- the no-op path for repeated `end_params` is exactly the intended chain semantics;
- otherwise the new value is `H(previous_chain || current_end_params)` with exact
  ordering and serialization;
- the updated value is written to the exact public-output registers later exposed
  by the outer proof.

At the inspected native snapshot, `compute_end_params` hashes a fixed block
containing final PC and then the flattened setup caps; the base chain hashes
`zero_digest || base_end_params`; extension is a no-op when the prior preimage's
end-parameter half already equals the current end parameters and otherwise hashes
`previous_hash || current_end_params`. Re-read these routines in the target version
and match their reduced-round setting and serialization.

### L1 terminus

- L1 checks the expected final chain value, not merely that some chain value was
  proved;
- the expected value commits to every allowed program/setup transition in the
  intended order;
- the outer verifier program/setup and success PC are fixed;
- the chain cannot begin at an arbitrary recursion step, truncate before the base,
  skip a required program version, reorder steps, or substitute another verifier
  program with the same output shape;
- the public base output and chain digest are not confused, swapped, or named
  according to stale register semantics;
- settlement consumes both the base state-transition output and the chain/version
  authorization required by policy.

The L1 contract normally does not need to re-hash every historical link. It may
verify one final proof and compare the chain terminus, provided the recursively
proved program enforces the base and step rules and L1 authenticates that program.

## 12. Contract-to-contract authentication

Inventory every `call`, `staticcall`, `delegatecall`, external Solidity call,
registry write, event, and return-data read.

For each call record:

| Caller | Target source | Opcode | Input | Success checked? | Returndata checked? | State effect | Security role |
|---|---|---|---|---|---|---|---|

Check:

- target address is fixed or authenticated;
- expected code exists and its runtime code hash/version is trusted;
- low-level `call`/`staticcall` return value is checked;
- required return length and canonical return encoding are checked;
- calls to a nonexistent account cannot count as verification success;
- callee revert, out-of-gas, and malformed return data cause rejection;
- no `delegatecall` lets verifier logic execute against attacker-controlled storage
  or through an unexpected proxy;
- callback/reentrancy cannot observe or finalize partial verification state;
- registry marking is limited to the designated GKR/WHIR verifier contracts or is
  cryptographically self-authenticating;
- marks are tied to verifier version, statement, and chain context;
- duplicate/idempotent calls cannot replace public data;
- the finalizer consumes a proof exactly as policy requires and cannot be replayed;
- events are not treated as authenticated state by an on-chain consumer.

Solidity low-level calls return a success flag instead of automatically bubbling
failure, and a call to a nonexistent account can report success. This is a mandatory
review item, not a style preference.

## 13. Public outputs and state-transition authorization

Trace every public output byte from the proved machine state to the L1 transition:

```text
committed trace/register tuple
  -> memory/permutation closure
  -> final register value and timestamp
  -> GKR public extraction
  -> split-proof commitment/registry storage or return data
  -> settlement comparison
  -> state-transition input
```

For Airbender's documented convention, registers `x10..x17` carry the base
program output and the next eight registers carry recursion-chain-related data.
Current EVM code names the second eight-register word `setup_commitment`; confirm
the current program ABI rather than trusting that name. Semantic-name drift at this
boundary is a high-priority substitution risk.

Audit:

- register index and little-/big-endian packing;
- high-bit cleanliness for each `u32` register;
- final register timestamps and their inclusion in memory closure;
- final PC equality and timestamp range;
- output digest preimage and application-specific L1 calldata;
- setup/program digest comparison;
- recursion-chain terminus comparison;
- old-state/new-state/chain-id/batch-number binding required by the rollup;
- exactly-once consumption and replay protection;
- whether a successful verifier transaction alone mutates rollup state or only
  records a pending proof;
- whether the final settlement call rechecks the same statement whose proof was
  marked.

## 14. Yul memory, stack spilling, and compiler behavior

Hand-written verifier Yul commonly violates normal Solidity allocation patterns for
gas reasons. Treat the memory map like unsafe code.

Create a lifetime map for every region:

| Region | Address formula | Size | Initialized before read? | Live interval | Writers/readers | Allowed overlap |
|---|---:|---:|---|---|---|---|

Include:

- free-memory pointer and Solidity-reserved scratch/zero slots;
- field modulus and permanent pointers;
- transcript seed and hash scratch;
- challenge arrays and MLE points;
- claims, gate caches, generated tables, Merkle leaves/paths/caps;
- preimage buffers and external-call calldata;
- return buffers;
- compiler-generated stack-spill regions under `viaIR`.

Check:

- every `mload` has a dominating complete initialization;
- partial-width `mstore` emulation cannot retain stale bytes;
- overlapping transcript/preimage writes do not hash old data;
- a helper does not clobber values live in its caller;
- loop bounds match allocated capacity;
- `mcopy`/`calldatacopy` source and destination overlap semantics are correct;
- memory expansion or pointer arithmetic cannot wrap;
- the free-memory pointer is preserved if any Solidity code relies on it;
- `assembly ("memory-safe")` actually obeys Solidity's documented memory model;
- the compiler's stack-to-memory spilling cannot overlap hand-placed scratch;
- generated circuit size changes cannot outgrow a hard-coded safe region;
- the exact `solc`, optimizer, and IR pipeline used for deployment is tested;
- all security-relevant known compiler bugs for that version/configuration are
  dispositioned.

The current Airbender heuristics intentionally hand-place memory and describe
`viaIR` spill interaction. Comments and a final free-memory-pointer guard are useful
evidence, but not a proof of non-overlap. Recompute region bounds from the largest
generated circuit and inspect the compiled Yul/EVM output.

## 15. EVM arithmetic and control flow

Yul `add`, `sub`, and `mul` operate modulo `2^256`; protocol arithmetic usually
operates modulo field prime `p`. Audit every expression not wholly inside `addmod`
or `mulmod` with an explicit integer bound.

Check:

- multiplication fits before any ordinary `mod`, or uses `mulmod`;
- addition cannot wrap before `mod(add(...), p)`;
- subtraction cannot underflow before reduction;
- operands advertised as reduced actually are;
- noncanonical running values have proven bounds before later ordinary arithmetic;
- extension-field coefficient operations use correct formulas/order;
- exponentiation/inversion handles zero and exceptional points;
- comparison is unsigned unless signed semantics are intended;
- shift amount is in range; shifts by 256 or more do not silently erase values;
- masks are correct for `u128`, `u64`, `u32`, query bits, and PoW thresholds;
- `pow_bits = 0`, maximum difficulty, and `256 - pow_bits` are safe;
- query/domain shifts cannot overflow or turn a mask into all ones;
- every equality result reaches `revert` on failure;
- no `return`, `stop`, fallthrough, or branch bypasses later checks;
- fallback/receive and call-value behavior are intentional;
- returned debug/gas/cursor words are never mistaken for an ABI `bool` success.

## 16. Merkle, WHIR, and grinding details

Apply the main PCS and grinding references, plus EVM-specific checks:

- Keccak input bytes are exactly the Rust Merkle leaf/node encoding;
- cap node order and witness/setup oracle order are fixed;
- base leaves transpose packed columns exactly as the Rust flattener;
- sibling order and query-index bits choose left/right consistently;
- path depth terminates at the cap, and cap index is range checked;
- every queried field lane is canonical before hashing and folding;
- intermediate caps and OOD samples are absorbed before the next challenges;
- terminal monomials are complete and degree bounded;
- final proof cursor exhausts calldata;
- repeated query indices and extraction bias match the soundness analysis;
- PoW nonce endian, threshold bits, seed mutation, and post-PoW draw match Rust;
- difficulty and schedule are generated from authenticated configuration, never
  calldata;
- gas optimization does not remove a check or leave its result unused;
- GKR-to-WHIR batching includes every merged memory/witness/setup claim once with
  the expected powers and order.

Grinding hardens only the challenge distribution. It does not authenticate a
registry mark, repair a missing recursion-chain check, or bind omitted statement
data.

## 17. Gas, code size, and liveness

Out-of-gas is normally rejection, not sound acceptance. It can still make the proof
system unusable or force a security-relevant architectural split.

Record:

- maximum proof calldata bytes and calldata gas under the target fork;
- maximum execution gas, memory expansion, and external-call gas;
- block/transaction gas assumptions;
- runtime and initcode sizes under the deployed fork;
- whether verifier splitting introduced persistent unauthenticated state;
- cold/warm account and storage access assumptions;
- worst-case but valid query/path/schedule behavior;
- whether prover-controlled values can increase loop work or allocation;
- gas forwarded to helper/registry calls and whether failure is handled;
- refund/revert/partial-state semantics;
- deployability and reproducibility on every supported chain.

Do not reduce soundness parameters to solve gas/code-size problems without a new
quantitative security budget. Do not classify an impossible-to-deploy generated
artifact as verified merely because its source-level test passes.

## 18. Differential and adversarial testing

An honest end-to-end proof test is necessary and insufficient. Build the following
defensive suite.

### Byte and parser mutations

- truncate at every field, nonce, cap, path, and final-tail boundary;
- append one byte, one word, and all-zero trailing regions;
- insert/delete a byte to test stream realignment;
- set every unused/high bit;
- use `p`, `p+1`, maximum `u128`, and alternate representatives;
- swap high/low field lanes and LE/BE `u32` words;
- alter each cap node, path sibling, query leaf, coefficient, and claimed output;
- test zero, singleton, maximum, and last-partial packing chunks;
- force each PoW boundary difficulty and nonce endian case.

### Cross-implementation properties

- Rust flattener byte length/order equals Yul cursor consumption;
- Rust and Yul expose identical transcript seeds/challenges at every checkpoint;
- generated GKR handoff preimage equals WHIR's parsed preimage byte-for-byte;
- Rust field/MLE/Merkle reference equations equal Yul on random small vectors;
- recursive native output/register encoding equals the on-chain extraction;
- solc settings used by tests equal deployment settings;
- generated runtime bytecode equals deployed code hash.

### Contract composition attacks

- call registry marking functions directly from an unauthorized account/contract;
- mark GKR and WHIR halves from different verifier deployments or versions;
- mark the same commitment twice with different public data;
- run only one verifier half, then attempt finalization;
- make registry/helper call revert, run out of gas, or target an empty account;
- reorder transactions, replay old commitments, and exercise stale partial state;
- finalize twice or on the wrong chain/session/batch;
- call through every proxy/fallback/selector path;
- verify the settlement caller rejects wrong output, setup, final PC, recursion-chain
  end, old state, and public calldata even when the cryptographic proof itself is
  valid for another statement.

### Compiler/memory tests

- compile with the exact pinned solc binary and settings;
- compare legacy and via-IR only as diagnostic targets, not interchangeable
  deployments;
- exercise the widest generated circuit and every memory-region boundary;
- use canaries around hand-placed regions in a test harness;
- compare optimized Yul/EVM disassembly around all rejection checks;
- run known-compiler-bug screening for the chosen release.

## 19. Audit artifacts

In addition to the main verifier skill's four artifacts, produce:

### Deployment trust map

```text
governance/deployer
  -> verifier implementation or proxy
  -> generated GKR contract
  -> generated WHIR contract
  -> registry/linker
  -> settlement/state-transition contract
  -> rollup state
```

Label immutable addresses, code hashes, upgrade keys, authorized callers, storage
slots, and which component owns final acceptance.

### Calldata/memory map

Provide byte offsets for the proof and lifetimes for Yul memory. Generated tables
may be attached separately, but every proof byte and every live memory region needs
a disposition.

### Cross-implementation relationship/parity table

| Obligation | Rust native | Rust flattener | GKR Yul | WHIR Yul | Registry/wrapper | Settlement | Status |
|---|---|---|---|---|---|---|---|

Include statement fields, transcript phases, field encoding, caps, PoW, GKR outputs,
PCS claims, memory products, final registers, final PC/timestamp, setup identity,
recursion chain, and rejection behavior.

### Persistent-state protocol table

For multi-transaction verification, list every storage transition:

| Prior state | Authorized caller | Input/commitment | Check | New state | Replay/overwrite rule | Finalizable? |
|---|---|---|---|---|---|---|

### Candidate disposition additions

For each candidate, state whether it survives actual compiler/deployment settings
and whether the settlement caller can reach an unauthorized state transition. A
bug in an unused prototype registry is not a production soundness finding; a
deployed registry accepted by settlement is.

## 20. Checklist and primary sources

### Statement and recursion

- [ ] exact L1 entrypoint and accepted statement are identified
- [ ] verifier program/setup and final PC are authenticated
- [ ] base output and recursion-chain terminus are separately decoded and checked
- [ ] base case, recursive step, no-op path, and final chain anchor match native semantics
- [ ] one-chunk/local-memory assumption is established, not guessed
- [ ] every inner/global invariant has already been closed or is completed on L1

### Parsing and algebra

- [ ] every calldata byte has a ledger row and final cursor is exact
- [ ] truncation cannot become accepted zero padding
- [ ] mixed endian and packed lanes match Rust exactly
- [ ] all proof field values are canonical or consistently reduced before hash/use
- [ ] all EVM-versus-field overflow/underflow bounds are proved
- [ ] every generated/hand-written rejection is reachable and unconditional

### Fiat-Shamir and PCS

- [ ] statement, caps, messages, and handoff values are absorbed in correct order
- [ ] challenge mapping, state advancement, and PoW match the concrete Rust path
- [ ] GKR and WHIR halves bind the complete same handoff state
- [ ] every merged base claim is opened through WHIR
- [ ] grinding is attached to the exact transcript prefix and not credited elsewhere

### Deployment and integration

- [ ] generator inputs and security parameters reach generated source exactly
- [ ] exact compiler/settings/runtime bytecode/deployed code hash are pinned
- [ ] memory-safe annotations and spill regions are valid for the deployed compiler
- [ ] registry/helper callers and callees are authenticated
- [ ] every low-level call success bit and required returndata are checked
- [ ] partial, reordered, replayed, duplicate, and overwritten marks are safe
- [ ] final settlement checks complete authenticated verification state
- [ ] proxies/upgrades/chain context cannot substitute a different verifier
- [ ] gas and code-size limits do not invalidate the deployed architecture

Primary implementation sources:

- [Solidity inline assembly and memory-safety rules](https://docs.soliditylang.org/en/latest/assembly.html)
- [Solidity ABI specification, strict mode, and packed-encoding ambiguity](https://docs.soliditylang.org/en/latest/abi-spec.html)
- [Solidity call/revert behavior](https://docs.soliditylang.org/en/latest/control-structures.html)
- [Solidity compiler options](https://docs.soliditylang.org/en/latest/using-the-compiler.html)
- [Solidity known compiler bugs](https://docs.soliditylang.org/en/latest/bugs.html)
- [Ethereum Yellow Paper](https://ethereum.github.io/yellowpaper/paper.pdf)
- [EIP-170 contract-code size limit](https://eips.ethereum.org/EIPS/eip-170)
- [EIP-211 return-data semantics](https://eips.ethereum.org/EIPS/eip-211)
- [ERC-1967 proxy implementation/admin slots](https://eips.ethereum.org/EIPS/eip-1967)

Use the chain's actual activated fork rules rather than assuming every proposed EIP
is live. Re-check these sources and the Solidity known-bugs list at the time of the
audit.

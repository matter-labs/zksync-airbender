# TRANS: Transcript construction

> The Fiat-Shamir state machine every proof in the system draws its challenges
> from: initial seed derivation, subsequent state transitions, the encoding of
> each absorbed class, and the absorbed order. Acceptance obligations are in
> [verifier.md](verifier.md); the open reduction is in
> [soundness.md](soundness.md).

## Transcript actions

Below L1, each transition hashes one complete message. A message may require
several compression calls. The transcript has four actions:

| Action | Input | Effect on `state` |
|---|---|---|
| `initialize(v)` | the encoded initial input `v` | `state ← H(v)` |
| `absorb(v)` | the encoded value `v` | `state ← H(state || v)` |
| `squeeze(n)` | nothing | emits `state` first; hashes `state` only for further digest words |
| `grind(b)` | one two-word nonce | `state ← H(state || nonce)`; output word `0` satisfies the work predicate |

The transcript produces challenge words and WHIR query-index bits. It consumes
only values explicitly initialized, absorbed, or used as grinding nonces.

## Symbols

- `H(M)` — a complete invocation of the transcript hash on message `M`:
  seven-round Blake2s below L1, Keccak256 on the Proth120 L1 path.
- `state` — the accumulated transcript digest. Below L1 it is `dig` words of
  `u32 = [0, 2^32)`; on the L1 path it is one 32-byte Keccak digest.
- `blk = 16` — the Blake2s input block, in `u32` words.
- `dig = 8` — the Blake2s digest, in `u32` words.
- `X || Y` — concatenation of word or byte vectors.
- `k ≥ 0` — the data-word count appended by one seeded transition.
- `n ≥ 1` — the word count of one `squeeze`.
- `b ∈ [0, 32]` — the proof-of-work bit count of one grinding stage below L1.
- `F` — base field; `E` — its degree-four extension for BabyBear targets.
- `c₀, c₁, c₂, c₃` — the base-field coordinates of an element of `E`, with `c₀`
  the low coordinate.

## Assumptions

- **ASM-TRANS-001 — Hash primitive.** `H` accepts a variable-length message and
  returns one digest. Below L1 it is evaluated through a fixed-width compression
  interface carrying the meaningful input length and final-block flag, with the
  round count reduced from ten to seven.
- **ASM-TRANS-002 — Enclosing interface.** On paths with external circuit
  challenges, those challenges and the setup identity are supplied by the enclosing
  verifier and are not re-read from the circuit's own proof stream. The packed
  Proth120 L1 path derives its product and lookup challenges internally.

## State transitions

### REQ-TRANS-002 — Initial seed derivation

For the ordered initial input `initial`, initialize the transcript from the hash
initialization vector with no state prefix:

`state_0 ← H(initial)`.

An implementation may stream `initial` through a buffering interface, but the
result must equal one hash of the complete concatenation. Buffering is an
evaluation strategy, not a second transcript construction.

### REQ-TRANS-001 — Seeded transition

After initialization, absorbing `data` replaces the state with

`state_(i+1) ← H(state_i || data)`.

Each transition starts a fresh hash invocation from the hash initialization
vector. Below L1 the `dig` state words precede the `k` data words. A long message
spans as many `blk`-word compression blocks as required under
`REQ-TRANS-VER-009`; it is not one compression call.

The same transition with empty `data` produces an additional digest during a
long squeeze. With the two-word nonce as `data`, it is the grinding transition.

### REQ-TRANS-003 — Absorbed value encoding

Below L1 every absorbed class is a whole number of `u32` words:

| Class | Encoded width | Element order |
|---|---:|---|
| raw word | `1` word | as read |
| element of `F` | `1` word | the element's internal reduced representation, not its canonical integer value |
| element of `E` | `4` words | coefficients `c₀, c₁, c₂, c₃` |
| hash digest, one Merkle-cap node | `dig` words | ascending word index |
| Merkle cap | `dig · (cap size)` words | ascending node index, then ascending word index |
| fixed-layout block | one whole `blk`-word block | class identifier and its payload at fixed word indices, remaining words zero |
| proof-of-work nonce | `2` words | low word, then high word, denoting `nonce = hi · 2^32 + lo` |

The fixed-layout block is the class the full-statement-verifier uses when a
class switch must land on a block boundary. Its instances are the class
identifier of `REQ-FSV-COM-004`, which occupies the leading word and, in the
unified format, carries that instance's initialization-window top bits in the
following words of the same block; and the final program counter with its split
timestamp, at fixed word indices of a block of their own.

On the Proth120 L1 path the absorber is byte-oriented: an element of `F` is its
16-byte big-endian canonical representation, a `u32` word of a transcript
preimage is four little-endian bytes, a digest is 32 bytes, and a nonce is eight
big-endian bytes. An absorb is `state ← Keccak256(state || data)`, the initial
commit hashes its data with no state prefix, and every `squeeze` advances the
state by `state ← Keccak256(state)` before emitting output.

## Absorbed order

### REQ-TRANS-004 — Circuit transcript order

One circuit transcript performs its actions in exactly this order. A nonce is
ground, a challenge or a query index is drawn, and every other entry is
absorbed:

1. one target-specific contiguous initial image, absorbed by the first action with no
   state prefix:
   - below L1: initialization-window top bits, flattened external challenges, then
     setup, memory, and witness Merkle caps;
   - packed Proth120 L1: 32 register-final-state triples, the final-PC/timestamp
     triple, initialization-window top bits, then setup and merged-memory caps;
2. below L1, the lookup-challenge nonce and then lookup `α, β`; on the packed
   Proth120 L1 path, the combined external/lookup nonce, then seven global-product
   challenges followed by lookup `α, β`;
3. the explicit global output pairs;
4. the dimension-reduction layers in descending layer index, then the circuit
   layers in descending layer index; within one layer, the internal-round
   Sumcheck coefficients, then the final-step at-point evaluations, then the
   evaluations the caching relations require, absorbed as one action before that
   layer's batching challenge is drawn;
5. on the packed path, the packing coordinates and the resulting claim merges; then
   the GKR-to-WHIR batching nonce and the WHIR batching challenge;
6. per non-final WHIR round: for each of its `k_i` Sumcheck steps, the coefficients
   then the coordinate; then the Merkle cap, out-of-domain point and reply, round
   nonce, query indices, and delinearization challenge;
7. in the final WHIR round: for each of its `k_(M-1)` Sumcheck steps, the
   coefficients then the coordinate; then the final polynomial's monomial
   coefficients, the final nonce, and the final query indices.

The top-bit count is a compiled constant of the circuit and is zero for a circuit that
carries no initialization window. Below L1, external challenges are absent from the
proof stream. On the packed Proth120 L1 path they are transcript outputs, not proof
fields.

## Ownership boundary

This module owns only transcript initialization, absorption, squeezing, and
grinding. Merkle hashing and recursion continuation hashing are separate
constructions owned by WHIR and recursion even when they select the same hash
primitive or reuse the same hashing helper. Transcript messages carry no
per-action label, prefix, or tag.

## Metadata

- profile: all targets

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `ASM-TRANS-001` | normative | every transcript action | hash-primitive boundary; `ASM-TRANS-SND-001` | selected hash configuration of the supported configuration |
| `ASM-TRANS-002` | normative | every circuit transcript | discharged by `REQ-FSV-COM-005` | implementation of the supported configuration |
| `REQ-TRANS-001` | normative | every transcript transition after initialization | `ASM-TRANS-001`; `GAP-TRANS-SND-001` | implementation of the supported configuration |
| `REQ-TRANS-002` | normative | every transcript initialization | `ASM-TRANS-001`; `GAP-TRANS-SND-001` | implementation of the supported configuration |
| `REQ-TRANS-003` | normative | every absorbed value | `REQ-TRANS-001`, `REQ-TRANS-002` | implementation of the supported configuration |
| `REQ-TRANS-004` | normative | every circuit transcript | `REQ-TRANS-001..003`; `ASM-TRANS-002` | implementation of the supported configuration |

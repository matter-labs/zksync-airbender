# TRANS-VER: Transcript verifier obligations

> What a conforming verifier must enforce over the transcript state machine:
> statement binding, reduction on read, causality, the position of every
> proof-of-work stage, challenge word mapping, and source-specific stream termination. Concrete
> proof-of-work bit counts belong to the selected target, not to this module.

## Imports

- `protocols/transcript/protocol.md`

## Guarantee

Under these obligations the initial state binds every part of the statement an
adversary may choose, no challenge is drawn before the messages it must bind
have been absorbed, no nonce is checked against a state other than its
scheduled one, and every consumed proof field occupies its scheduled position. Only
the Proth120 L1 calldata path additionally guarantees rejection of a trailing suffix.

## Symbols

- `state`, `absorb`, `squeeze`, `grind`, `blk = 16`, `dig = 8`, `H` — as defined
  in [protocol.md](protocol.md).
- `w ∈ u32` — a single transcript output word.
- `n ≥ 1` — the word count of one `squeeze`.
- `p` — the base-field characteristic; `2^32 < 3p` for BabyBear.
- `b ∈ [0, 32]` — the proof-of-work bit count of one grinding stage below L1.
- `digest[i]` — word `i` of a compression output, `i ∈ [0, dig)`.

## Decision tree

> Navigation view only; leaf IDs name the canonical statements. Interpret the
> tree under `ASM-TRANS-001..002`.

- **Before the first challenge of a proof.** Bind every adversary-chosen part of
  the statement under `REQ-TRANS-VER-013`.
- **Next scheduled transcript action.**
  - **Absorb a proof value.** Encode it at the width and element order of
    `REQ-TRANS-003`, reduce a value read as a field element under
    `REQ-TRANS-VER-001`, frame and pad it under `REQ-TRANS-VER-009`, in the
    position fixed by `REQ-TRANS-004` under `REQ-TRANS-VER-006`.
  - **Squeeze a challenge.**
    - **Every message the challenge binds has been absorbed.** Draw it under
      `REQ-TRANS-VER-002` and map its words to coordinates or query-index bits
      under `REQ-TRANS-VER-010`, and, for the lookup and WHIR batching
      challenges, only after the schedule points of `REQ-TRANS-VER-003` and
      `REQ-TRANS-VER-004`.
    - **Some bound message is still unabsorbed.** Rejected schedule; not a
      runtime branch.
  - **Grind a nonce.** Verify it against the state at its exact scheduled
    position under `REQ-TRANS-VER-005`, with the encoding of
    `REQ-TRANS-VER-011`, from the inventory of `REQ-TRANS-VER-008`.
  - **Absorb or draw on the Proth120 L1 path.** Use the byte encoding and
    reduced-value binding of `REQ-TRANS-VER-012` instead of the word encoding.
  - **Consume a challenge transported through the proof stream.** Recompute it
    from `state` and reject on inequality under `REJ-TRANS-VER-002`.
  - **Scheduled fields are consumed.** Enforce source-specific termination under
    `REQ-TRANS-VER-007`; only the L1 calldata path rejects an unread suffix.

## Requirements

### REQ-TRANS-VER-013 — Statement binding

Every part of the statement an adversary may choose is absorbed before the first
challenge is drawn. Below L1 this is the setup identity, memory and witness
commitments, initialization-window top bits, and external challenges supplied by the
enclosing verifier. On the packed Proth120 L1 path it is the register final state,
final PC and timestamp, initialization-window top bits, setup cap, and merged-memory
cap; the product and lookup challenges are then derived internally. The first action
of `REQ-TRANS-004` absorbs the applicable image together, so no challenge is drawn
from a state that omits any of it.

A transcript that omits a chosen part of the statement admits the standard
attack on the omitted part: a transcript is produced first and the omitted part
is then solved for, in time linear in its size for an evaluation-form check.

### REQ-TRANS-VER-001 — Reduction on read

Absorb each value at the width and element order fixed by `REQ-TRANS-003`.
Merkle cap and Merkle path words are absorbed raw, without reduction.

Unless a target states canonical encoding, a proof word read as a field element
is reduced into the field's internal representation:

`x ← w mod p`.

For BabyBear, `2^32 < 3p`, so a host may implement the reduction with at most two
conditional subtractions; the RISC-V verifier may use an equivalent `mop.rr`
reduction. Every `u32` maps to a field element, and the two or three words congruent
to one residue are indistinguishable after reduction. Canonicity of `w` is a
prover-side contract, not a verifier check.

The word absorbed for an element of `F` is the element's internal reduced
representation. For BabyBear that representation is not the canonical integer
value, so the transcript binds the internal encoding rather than the residue's
decimal value. Any restatement of this module that says "canonical
representation" is wrong.

### REQ-TRANS-VER-002 — Causality

Draw a challenge only after absorbing every message and commitment it must bind:

`c ← squeeze(state)` is admissible only when `state` includes every message on
which the relation checked with `c` depends.

### REQ-TRANS-VER-003 — Lookup order

Verify lookup-challenge proof-of-work after the initial commitments and before
drawing lookup challenges or reading explicit output evaluations:

`initial image → grind(pow_lookup) → squeeze(alpha, beta together) → explicit outputs`.

On the packed Proth120 L1 path the same post-nonce draw sequence yields seven
global-product challenges immediately before lookup `α, β`, with no absorb between
the nine elements.

### REQ-TRANS-VER-004 — WHIR order

Process all GKR messages and, on the packed path, draw the packing coordinates and
merge the base-column claims. Then perform the GKR-to-WHIR batching proof-of-work before
drawing the WHIR batching challenge and entering WHIR:

`GKR layers → packing coordinates and merge → grind(pow_batch) → squeeze(gamma_whir) → WHIR`,

with the packing step omitted on unpacked paths.

### REQ-TRANS-VER-005 — Proof-of-work state

Verify each nonce against the transcript state at its exact scheduled position.
Later challenge words exclude every word constrained by proof-of-work and every
word already consumed as a query index. The encoding and the identity of the
constrained word are `REQ-TRANS-VER-011`.

### REQ-TRANS-VER-006 — Component reads

Each verifier component reads exactly its scheduled fields. A finite host stream
rejects underflow. A CSR stream cannot signal end-of-stream, so the verifier consumes
the compiled prefix without claiming that its length is authenticated.

### REQ-TRANS-VER-007 — Exhaustion

Unread trailing words in the host and CSR proof sources are not transcript-bound and
are not rejected; they are inert suffix data outside the parsed proof. On the
Proth120 L1 path, the enclosing verifier rejects a trailing suffix by comparing the
calldata size for equality with the final consumed offset.

### REQ-TRANS-VER-008 — Proof-of-work inventory

The scheduled grinding stages are:

| Stage | Position |
|---|---|
| lookup-challenge proof-of-work | before the lookup challenges |
| GKR-to-WHIR batching proof-of-work | before the WHIR batching challenge |
| each scheduled WHIR-round proof-of-work | before that round's queries |
| full-statement-verifier memory/delegation proof-of-work | before the external challenges |
| Proth120 wrapper external-challenge proof-of-work | before the wrapper's external challenges |

The bit count of each stage is fixed by the selected target.

### REQ-TRANS-VER-009 — Block framing and padding

Absorption is word-granular into a `blk`-word input block. The initial message
uses `REQ-TRANS-002`; each later message prepends the current state under
`REQ-TRANS-001`. A block is compressed when it fills and more data remains; the
trailing partial block is zero-filled to `blk` words and compressed as the final
block, with the hash's byte counter counting only the meaningful words.
Zero-filling a partial block is the padding rule, not an error, and the byte
counter distinguishes messages whose zero-filled blocks are equal.

A verifier that requires a class switch to land on a block boundary absorbs each
class identifier as one whole zero-padded `blk`-word block. The
full-statement-verifier instance of that requirement is `REQ-FSV-COM-008`.

### REQ-TRANS-VER-010 — Challenge word mapping

One `squeeze` yields the `dig` words of the current `state` in ascending index
without recomputing the hash. Drawing more than `dig` words recomputes it,

`state ← H(state)`,

which is `REQ-TRANS-001` at `k = 0`, and yields the next `dig` words; a draw of
`n · dig` words therefore returns `state, H(state), …, H^(n-1)(state)` and
leaves `state ← H^(n-1)(state)`. The last digest a draw returns is always the
state the next draw begins from, so two draws with no intervening `absorb` or
`grind` overlap in one full digest. That overlap is the condition of
`DEV-TRANS-001`.

An element of `E` is assembled from four consecutive drawn words: word `j` of
the group becomes coordinate `c_j`, with the first word the low coordinate `c₀`.
Each word is converted by the reduction of `REQ-TRANS-VER-001`; no word is
rejected for being at least `p`, so the sampled distribution is the biased one
named by `GAP-TRANS-SND-005`.

A WHIR query index is taken from the drawn words read as a little-endian bit
stream: bit `i` is bit `i mod 32` of word `⌊i / 32⌋`, counting from the first
word the draw admits after the exclusion of `REQ-TRANS-VER-005`. Indices are
taken sequentially at the round's index bit width, masked to that width, with no
rejection sampling; the index is uniform only because the evaluation domain has
power-of-two size.

### REQ-TRANS-VER-011 — Grinding encoding

A nonce is a `u64` carried as two words, low word first, denoting
`nonce = hi · 2^32 + lo`. Verification is `REQ-TRANS-001` at `k = 2`: it places
the `dig` `state` words at block words `0..dig`, `lo` at word `dig`, `hi` at
word `dig + 1`, zeroes the remaining words, and compresses `dig + 2` meaningful
words as a final block. Acceptance requires

`digest[0] ≤ 2^(32-b) − 1`,

that is, `b` leading zero bits of the numeric value of output word `0`, and
`b ≤ 32` because only one word is constrained. The resulting digest replaces
`state`, so a grinding stage also advances the transcript.

Word `0` is the word the condition constrains. Every draw scheduled after a
grinding stage skips it and starts at word `1`, as required by
`REQ-TRANS-VER-005`, and a draw sized for `n` words after a stage draws
`n + 1` words rounded up to a multiple of `dig`.

Execution at `b = 0` differs by path. On the GKR and WHIR paths the stage is
still executed: its two nonce words are read, its compression still advances
`state`, and word `0` is still skipped. On the full-statement-verifier path the
stage is skipped when `b = 0`: no compression is performed and word `0` is not
skipped, while the two nonce words are still read from the proof stream and left
unbound. Every supported target fixes a nonzero bit count for that stage.

On the Proth120 L1 path the nonce is eight big-endian bytes appended to the
state, and the condition is `b` leading zero bits of the 256-bit big-endian
digest, so `b` is not capped at `32` there.

### REQ-TRANS-VER-012 — L1 byte encoding

On the Proth120 L1 path the absorber is byte-oriented over Keccak256, with the
widths and orders of `REQ-TRANS-003`. Every `squeeze` first advances the state,
`state ← Keccak256(state)`, and the drawn element is the digest's leading 16
bytes read big-endian and reduced modulo `p`. No digest is ever returned twice,
so `DEV-TRANS-001` does not arise on this path.

A 16-byte lane is not a canonical encoding of a `Proth120` element:
`p = 7·2^120 + 1 < 2^123`, so a residue has `⌊2^128 / p⌋ = 36` or `37` lanes. The
transcript must bind the reduced field value unambiguously. A call site may reduce or
canonicalize before absorption, or absorb the raw lane and reject a noncanonical lane
before using it; the implementation need not use one universal mechanism. Digest
lanes used for transcript draws are not prover-supplied and are reduced modulo `p`.

Accepting prover-selected aliases while absorbing their distinct raw lanes would give
about `5.2 · n` bits of free transcript grinding across `n` such lanes at unchanged
algebraic claims. The supported verifier must not expose that choice.

## Rejections

- **REJ-TRANS-VER-001 — Nonce at the wrong state.** Reject a nonce that
  satisfies the bit condition at any state other than its scheduled one.
- **REJ-TRANS-VER-002 — Prover-selected challenge.** Reject any query index or
  challenge whose accepted value is not the one `squeeze` produces at its
  scheduled position. A challenge may be transported through the proof stream,
  as the external challenges of `REQ-FSV-COM-005` are, provided the verifier
  recomputes it from `state` and rejects on inequality.

## Outputs

- **OUT-TRANS-VER-001 — Ordered challenge sequence.** The ordered challenges
  consumed by `REQ-SUM-VER-003`, `REQ-GKR-VER-007`, and `REQ-WHIR-VER-005`, each
  with the set of messages it binds.

## Metadata

- profile: all targets

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `REQ-TRANS-VER-013` | normative | before the first challenge of every proof | `REQ-TRANS-004`; `ASM-TRANS-002` | [Thaler, *Proofs, Arguments, and Zero-Knowledge*](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf), strong Fiat-Shamir |
| `REQ-TRANS-VER-001` | normative | every absorbed value | `REQ-TRANS-003` | implementation of the supported configuration |
| `REQ-TRANS-VER-002` | normative | every squeezed challenge | `REQ-TRANS-VER-001` | Fiat-Shamir causality requirement |
| `REQ-TRANS-VER-003` | normative | lookup challenges | `REQ-TRANS-VER-002`; `REQ-TRANS-VER-005` | implementation of the supported configuration |
| `REQ-TRANS-VER-004` | normative | WHIR batching challenge | `REQ-TRANS-VER-002`; `REQ-TRANS-VER-005` | derived from `REQ-GKR-VER-008` |
| `REQ-TRANS-VER-005` | normative | every grinding stage | `REQ-TRANS-VER-002` | project decision: nonce is bound to its scheduled state |
| `REQ-TRANS-VER-006` | normative | every verifier component | `REQ-TRANS-VER-001`, `REQ-TRANS-004` | compiled proof-stream parsing |
| `REQ-TRANS-VER-007` | normative | end of a proof source | `REQ-TRANS-VER-006` | source-specific termination behavior |
| `REQ-TRANS-VER-008` | normative | selected target | `REQ-TRANS-VER-005` | implementation of the supported configuration |
| `REQ-TRANS-VER-009` | normative | every absorbed value | `REQ-TRANS-001`, `REQ-TRANS-002`; `REQ-FSV-COM-008` | implementation of the supported configuration |
| `REQ-TRANS-VER-010` | normative | every squeezed challenge and query index | `REQ-TRANS-001`, `REQ-TRANS-VER-005`; `GAP-TRANS-SND-005`; violated by `DEV-TRANS-001` | implementation of the supported configuration |
| `REQ-TRANS-VER-011` | normative | every grinding stage | `REQ-TRANS-001`, `REQ-TRANS-VER-005`, `REQ-TRANS-VER-008` | implementation of the supported configuration |
| `REQ-TRANS-VER-012` | normative | Proth120 L1 path | `REQ-TRANS-003`, `REQ-TRANS-VER-001` | implementation of the supported configuration |
| `REJ-TRANS-VER-001` | normative | every grinding stage | `REQ-TRANS-VER-005`, `REQ-TRANS-VER-011` | derived from `REQ-TRANS-VER-005` |
| `REJ-TRANS-VER-002` | normative | every challenge and query index | `REQ-TRANS-VER-002`, `REQ-TRANS-VER-010`; `REQ-FSV-COM-005` | derived from `REQ-TRANS-VER-002` |
| `OUT-TRANS-VER-001` | normative | every proof | `REQ-TRANS-VER-001..013` | derived from `REQ-TRANS-VER-002` |

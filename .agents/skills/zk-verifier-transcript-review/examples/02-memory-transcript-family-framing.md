# Memory transcript omitted family and delegation framing

## Classification

- Confirmed historical cross-proof transcript-coverage bug
- Component: unrolled memory/delegation Fiat-Shamir transform
- Security character: missing statement and participant binding in challenges shared by global arguments
- Fixed by: [`386ab26`](https://github.com/matter-labs/zksync-airbender/commit/386ab2621f484cd8d923acbbf3e00467c8bd46ae)
- Vulnerable revision: `6be5025cc072e7ae503726a77d4cc0be1fd59577`

## Protocol context

The memory and delegation challenges are shared across independently proved circuit chunks. Those chunks contribute products to a later global equality rather than closing the argument locally. The challenge seed must therefore bind both the committed data and the semantic roster of participants whose products will be combined.

The relevant public state includes the final register values and their timestamps plus final PC. Commitment groups belong to distinct machine-circuit families, the inits/teardowns circuit, and delegation types. A flat sequence of caps is insufficient because position only has meaning relative to a canonical, tagged participant list.

## Intended transcript relation

The fixed transform constructs a canonical stream conceptually equivalent to:

```text
32 * (final register value, timestamp low limb, timestamp high limb)
final PC
for each nonempty machine family in canonical order:
    family tag || memory caps
inits/teardowns family tag || its caps
for each nonempty delegation type in canonical order:
    delegation type || delegation memory caps
```

Each logical item is encoded into the hash function's fixed-width framing. Empty-group behavior and ordering must be identical in prover, Rust verifier, recursive verifier, and any L1 reconstruction.

## Failure

The earlier memory transcript did not bind the complete framing later introduced by the fix: final register values/timestamps, final PC, machine circuit-family identifiers, the inits/teardowns family tag, and delegation types in sorted order.

This left two distinct ambiguities. First, global state consumed by the memory closure could vary independently of the random compression challenges. Second, an identical flattened cap sequence could be assigned to different circuit or delegation owners without changing the seed. Sorting a host collection or later selecting a verifier does not bind that ownership cryptographically.

## Adversarial flow

1. Fix the same sequence of commitment caps.
2. Change a final-state word, or reinterpret a cap group as another family/delegation type wherever the surrounding proof layout permits it.
3. Derive the same memory/delegation challenges because the changed semantic data is absent from the transcript.
4. Use those challenges in local product claims and in the final global accumulator check.

The final product equality only checks algebra under the shared challenge. It cannot retroactively prove that the challenge committed to the intended state or participant ownership.

## Impact and fix

The bug weakened the binding between global memory products, public final state, and their proof participants. It created cross-proof semantic aliasing at the exact point where independent chunks are probabilistically compressed into one global check.

The fix defines one canonical transform over final state and explicitly tagged cap groups. Machine families and delegation types are traversed deterministically, and only nonempty groups are represented according to a shared convention. The verifier mirrors this framing before entering the corresponding proof groups.

The broader lesson is that type tags, lengths, empty-group markers, participant counts, and public boundary state are transcript data whenever they determine the semantics of a later check. They are not harmless parser metadata.

## Regression

- Preserve every cap while mutating one final register value, timestamp limb, or final PC; require different shared challenges.
- Preserve caps and swap two family or delegation owners; require different seeds or canonical rejection.
- Feed the same logical map in multiple insertion orders and require the same canonical seed.
- Cover empty, singleton, and several-family/delegation cases in prover/verifier transcript-trace parity tests.
- Verify that the final global product check uses the challenges derived from this exact framed prefix.

## Reproduction evidence

```sh
git diff 6be5025cc072e7ae503726a77d4cc0be1fd59577 386ab2621f484cd8d923acbbf3e00467c8bd46ae -- circuit_defs/trace_and_split/src/lib.rs full_statement_verifier/src/unrolled_proof_statement.rs
```

# Unrolled transcript omitted machine-family and inits/teardowns owner tags

## Classification

- Confirmed historical latent transcript-framing defect
- Component: unfinished unrolled full-statement memory/delegation transcript
- Verifier anchor: private `full_statement_verifier/src/unrolled_proof_statement.rs` verifier path
- Exact omission: nonempty main-family tags and the nonempty
  inits/teardowns-family tag
- Reachability at the vulnerable revision: not integrated; the private verifier
  function had no caller or corresponding verifier artifact
- Security character if activated: conditional semantic aliasing between
  differently owned cap groups sharing one global challenge
- Fixed by:
  [`386ab26`](https://github.com/matter-labs/zksync-airbender/commit/386ab2621f484cd8d923acbbf3e00467c8bd46ae)
- Vulnerable revision: `6be5025cc072e7ae503726a77d4cc0be1fd59577`

## Exact affected code

The private verifier routine was
`full_statement_verifier/src/unrolled_proof_statement.rs::verify_full_statement_for_unrolled_circuits`.
In the main-family loop it read a proof count, verified that many proofs, and
absorbed each proof's flattened memory caps. It destructured the family value as
`_circuit_family` and never absorbed it:

```text
for each configured main family:
    num_circuits = read_word()
    repeat num_circuits times:
        verify family proof
        absorb family proof memory caps
```

The same routine then read the inits/teardowns proof count and absorbed those
proofs' memory caps without first identifying that group:

```text
num_inits_and_teardowns = read_word()
repeat num_inits_and_teardowns times:
    verify inits/teardowns proof
    absorb its memory caps
```

Commit `386ab26` added exactly these verifier-side framing elements:

```text
if a main family is nonempty:
    absorb pad16(circuit_family)

if the inits/teardowns group is nonempty:
    absorb pad16(INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX)
```

The commit also added the dedicated prover helper
`fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits`, which
uses the same owner-tagged schedule. There was no earlier same-instance
unrolled helper whose one-line omission this patch corrected; the new helper
completed the prover side of an unintegrated path.

## What was already present

Do not attribute unrelated transcript elements to this defect:

- The verifier already absorbed all 32 final register values and their two
  timestamp limbs.
- The verifier already absorbed final PC in a padded Blake2s block.
- Nonempty delegation groups were already prefixed by their delegation-type
  tags.
- The existing generic prover helper already absorbed registers/timestamps and
  delegation tags, but it was not a same-instance mirror: it absorbed a main
  setup cap, omitted final PC, and had no unrolled family or inits/teardowns
  roster.

The historical change therefore concerns ownership framing for main-family and
inits/teardowns caps, not omission of the complete public state or delegation
identity.

## Intended invariant

The shared memory/delegation challenge seed should encode both each cap and the
participant that owns it:

```text
registers and timestamps
final PC
for each nonempty main family in canonical order:
    main-family tag || that family's memory caps
if inits/teardowns is nonempty:
    inits/teardowns tag || its memory caps
for each nonempty delegation type in canonical order:
    delegation-type tag || that type's memory caps
```

Tags are padded to the buffering transcript's fixed Blake2s block width. Empty
groups omit both tag and caps in prover and verifier.

## Failure

Without the two missing owner tags, the outer transcript reduced main and
inits/teardowns participants to one flat sequence of fixed-width caps. For
example, these logical rosters had the same outer transcript bytes:

```text
family A: [cap_1]
family B: [cap_2]

family A: [cap_1, cap_2]
family B: []
```

Both became `cap_1 || cap_2`. The challenge therefore did not itself bind the
proof-supplied group boundaries or cap ownership.

This is not an established end-to-end forgery. A concrete reassignment also
has to survive the family-specific parser, generated verifier, and trusted
setup-cap comparisons. Those checks may make the two rosters incompatible.
The missing tags nevertheless left the global challenge without the intended
semantic domain boundary if a compatible pair or future integration made the
alternative roster reachable.

## Why this is latent

At `6be5025c`, repository-wide symbol search finds only the private function's
definition and no caller. No public wrapper or built verifier artifact in that
snapshot selected it. The fix commit added the dedicated prover transcript
helper, but that helper likewise had no call site in the fix snapshot.

Accordingly, classify this as a concrete defect in unfinished source with a
clear activation condition—not as a vulnerability in an accepted proof path.
It becomes security-relevant when a public verifier connects this unrolled
routine and relies on the owner-sensitive shared challenge without an
equivalent authenticated enclosing binding.

## Impact and fix

If activated without an equivalent enclosing identity check, the omission
would leave the shared memory challenge insensitive to cap ownership across
compatible groupings. The fix prefixes every nonempty main-family and
inits/teardowns cap group with
its canonical owner tag and defines a matching unrolled prover transform.

### Regression properties

Regression coverage should:

- compare prover and verifier transcript traces for empty, singleton, and
  multi-proof groups;
- hold cap bytes fixed while changing their family/group ownership and require
  a different seed or structural rejection;
- cover empty-to-nonempty transitions for every family and inits/teardowns;
- prove that fixed dispatch, setup authentication, or an enclosing program hash
  closes any case in which an explicit tag is intentionally omitted; and
- rerun reachability analysis whenever the private routine or helper gains a
  caller or generated artifact.

## Reproduction evidence

```sh
git diff 6be5025cc072e7ae503726a77d4cc0be1fd59577 386ab2621f484cd8d923acbbf3e00467c8bd46ae -- circuit_defs/trace_and_split/src/lib.rs full_statement_verifier/src/unrolled_proof_statement.rs
git grep -n verify_full_statement_for_unrolled_circuits 6be5025cc072e7ae503726a77d4cc0be1fd59577
git grep -n fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits 386ab2621f484cd8d923acbbf3e00467c8bd46ae
```

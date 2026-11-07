# Sparse delegation layout emitted a tuple where an Option was required

## Classification

- Implementation history: confirmed generator build defect before any verifier artifact existed
- Component: token serialization of one-row compiler indirect-access layouts
- Reduction location: compiler layout metadata → generated verifier/circuit Rust source
- Security character: fail-closed generation/compilation error, not a verifier false-acceptance bug
- Fixed by: [`9b955b6`](https://github.com/matter-labs/zksync-airbender/commit/9b955b649cfbd1ef04305ec15af344dc5a41354f)
- Vulnerable revision: `6327a202048659bd8afac3b65cf65bb7e2ed9fc3`

## Protocol context

`IndirectAccessColumns::{ReadAccess, WriteAccess}` stores an optional variable-dependent address term. Constant-only layouts use `None`; sparse variable-dependent layouts use `Some((coefficient, variable_column, auxiliary_index))`.

The compiler implements `quote::ToTokens` so layouts can be embedded into generated Rust artifacts. This serializer is a typed boundary: emitted tokens must reconstruct the exact enum/option structure, not merely print the tuple's contents.

## Intended serialization relation

```text
source variable_dependent = None
    -> generated `variable_dependent: None`

source variable_dependent = Some((c, v, i))
    -> generated `variable_dependent: Some((c, v, i))`

parse/typecheck(generated tokens) == source layout
```

Read and write variants must round-trip identically.

## Failure

For the `Some` branch, token generation emitted `variable_dependent: (c, v, i)` without the `Some(...)` constructor even though the field type was `Option<(...)>`. The generated artifact was malformed Rust for any variable-dependent indirect access.

The constant-only `None` branch still worked, so existing generated circuits without sparse offsets did not reveal the bug.

## Failure flow

1. Compile a circuit containing a variable-dependent sparse read or write.
2. Serialize its `IndirectAccessColumns` layout to Rust tokens.
3. Emit a bare tuple into an `Option`-typed field.
4. Fail generated-source compilation before a verifier artifact exists.

There is no accepted-proof soundness impact in this historical path because the malformed artifact fails closed. It belongs in this corpus as a generator provenance and coverage failure, not as a cryptographic vulnerability.

## Impact and fix

Affected sparse delegation circuits could not obtain a valid regenerated verifier/layout artifact. The fix wraps the tuple in `Some(...)` for both read and write variants while leaving constant-only `None` unchanged.

Generator review must include buildability and semantic round-trip tests for every enum variant. Reviewing only currently checked-in generated output can miss branches that fail when a new circuit activates them.

## Regression

- Serialize and compile read/write layouts with both `None` and `Some` variable dependencies.
- Parse or instantiate the generated value and compare every field with the source layout.
- Exercise nontrivial coefficient, variable-column, and auxiliary-index values.
- Require generated verifier CI after circuit-layout changes.
- Keep this case classified as completeness unless a permissive parser/default later turns malformed metadata into acceptance.

## Reproduction evidence

```sh
git diff 6327a202048659bd8afac3b65cf65bb7e2ed9fc3 9b955b649cfbd1ef04305ec15af344dc5a41354f -- cs/src/one_row_compiler/mod.rs
```

# Unified inits/teardowns used placeholder address windows

## Classification

- Confirmed historical unified-memory composition bug
- Invariant: inits/teardowns instances partition exactly the RAM address windows used by execution chunks
- Component: unified GPU proof inputs and execution-prover orchestration
- Security character: global permutation incompleteness under the historical geometry; `top_bits` are also transcript-relevant ownership metadata
- Fixed by: [`1581753`](https://github.com/matter-labs/zksync-airbender/commit/158175327734b2b865deb24dd7ea5a1b063abd65), PR [#389](https://github.com/matter-labs/zksync-airbender/pull/389)
- Vulnerable revision: `ae3c9adba438afbce0a2d94d91931dfd8082c2bd`

## Composition context

The inits/teardowns circuit supplies the boundary side of the global RAM permutation: initial values/timestamps and final values/timestamps for touched address regions. Each instance receives `top_bits` identifying its global address windows plus page indices local to those windows.

The dedicated inits/teardowns circuit and the unified circuit have different geometries. The dedicated shape covers 16 sets over a large contiguous address space. A unified instance covers two sets, and the complete statement distributes 32 windows across multiple instances over the same RAM.

Because the window identifiers determine which addresses a commitment represents—and are absorbed into the relevant transcript—they are part of both composition semantics and Fiat-Shamir framing.

## Intended invariant

Across all unified inits/teardowns instances:

```text
union(instance.global_windows) == configured RAM windows
windows are disjoint under the declared partition
each local page index maps to exactly one address inside its instance windows
the I/T contribution for each touched word pairs with execution's RAM contribution
transcript absorbs the actual top_bits assigned to that instance
```

Dedicated-circuit constants may be reused only after proving the geometries identical.

## Failure

Unified GPU proving supplied canonical placeholders `0..num_sets` for `top_bits`. Those indices describe the dedicated 16-set circuit, not a unified instance's two sets selected from 32 global RAM windows. The pipeline also fed page indices in the wrong global/local geometry.

As a result, each proof committed to address partitions different from those used by execution chunks. The implementation effectively overpacked pages by the ratio between the dedicated and unified layouts rather than assigning each instance its actual window pair.

## Failure flow

1. Split touched RAM pages among unified inits/teardowns instances.
2. Replace each instance's real global window identifiers with local placeholders beginning at zero.
3. Interpret page indices using the dedicated-circuit geometry.
4. Commit and absorb those incorrect partitions.
5. Aggregate execution RAM products with boundary products referring to different encoded addresses.
6. Fail the final memory permutation closure, often only in a full end-to-end or recursion-bridge proof.

The historical evidence establishes a completeness/global-closure failure. A soundness review must additionally ensure the verifier binds and validates window assignment so a malicious prover cannot choose overlapping or omitted windows that still close.

## Impact and fix

Unified proofs did not cover the same RAM relation as execution chunks, blocking final permutation closure and downstream recursion integration. The fix carries the real per-instance `top_bits`, converts global page assignment to correct local indices, and preserves those identifiers through proof input and transcript construction.

Audit address partitioning with concrete set arithmetic. Names such as `num_sets`, `page_index`, and `top_bits` are not interchangeable across circuit layouts.

## Regression

- Enumerate every configured RAM window and assert complete, disjoint ownership across instances.
- Place nontrivial touched pages in the first and last window of every instance.
- Round-trip `(top_bits, local_page_index)` to global address and require exact equality with execution's address encoding.
- Close the full RAM product, not merely each local I/T proof.
- Mutate, duplicate, or omit one instance's `top_bits` and require transcript change plus verifier rejection.
- Cover dedicated and unified geometries in separate fixtures so constants cannot silently cross over.

## Reproduction evidence

```sh
git diff ae3c9adba438afbce0a2d94d91931dfd8082c2bd 158175327734b2b865deb24dd7ea5a1b063abd65 -- gpu/circuit_prover/src/proof/inputs.rs gpu/execution_prover/src/prover/pipeline.rs
```

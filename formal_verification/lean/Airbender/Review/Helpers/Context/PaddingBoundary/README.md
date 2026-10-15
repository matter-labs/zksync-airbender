# External contribution-mask boundary

[Model](Model.lean) records the enforced GKR gate and exact logical closure over
all native row occurrences. [Theorems](Theorems.lean) checks its algebra and derives
ordinary active-trace acceptance; [implementation](../../../../Proofs/PaddingBoundary.lean)
contains identity erasure and padding insertion. The user authorized this external
boundary on 15 October 2026, analogous to the
[canonical verifier-PC binding](../VerifierBoundary/README.md).

## Contract and checked result

`mask execute input = 1 + execute * (input - 1)`. At zero it is one, and at one it
preserves the input. `contribution` represents identity as `none` and an entire
native tuple as `some tuple`; a zero-valued active tuple remains `some tuple`.
`product_soundness` proves that these symbolic factors agree with masking the
aggregate product for a Boolean selector. It holds for arbitrary tuple encodings
and values, without operand or result assumptions.

`Binding` retains the whole unfiltered layout and uses each row's actual imported
execute column. It supplies Booleanity and exact masked PC/memory permutations,
with the public initial/terminal contributions unmasked. `AcceptedLayout` also
checks imported constraints and every retained auxiliary/range/timestamp query
for every raw row. Active decoder membership stays in the existing public APIs;
no original instruction is required for inactive decoder padding.

`acceptance_soundness` erases identity factors and derives `Trace.Accepted` for
`active trace`. Selection preserves native occurrence order and multiplicity,
including duplicate padding rows. All public initial/terminal tokens, modeled
tables and full raw active tuples are unchanged. No inactive PC, timestamp, write
or result is required to stutter. Padding insertion is proved from execute zero
and the actual constraints, rather than assumed to preserve execution.

[Unified machine/worker binding](../../UnifiedReduced/PaddingBoundary.lean)
separately closes architectural GPR/RAM and full-width virtual CSR requests,
using the same native machine and worker selectors. All four worker layouts are
covered. Invocation clock zero is not a padding selector: execute-one unissued
workers retain their actual effects. Both invalid bigint controls remain admitted.
The [whole-execution entries](../../../Trace/Padding.lean) reuse restricted Sail,
six-family native boot/ROM, unified standard/TRIADD/XORROT execution and the
existing mixed caller observation certificate. Public configuration, domains,
canonical verifier-PC closure, discarded-load profiles, modeled tables, field
minima and inverses retain their existing scopes. Full custom-CSR execution and
native worker ROM transport are not added by this boundary.

## External meaning and provenance

The exact tuple permutations in `Binding` are external logical assumptions.
Mask algebra alone, or equal products at sampled challenges, does not imply them.
No project axiom is introduced: the theorems take the named contract as an input.
Address-space projection, binding compiled selector copies to native execute
columns, GKR/commitment/sumcheck soundness and Rust/artifact correspondence remain
external. The new boundary conditionally resolves architectural padding erasure;
it does not prove the Rust verifier implementation correct.

The source was inspected at checkout `4a12ba264` before this FV-only change.

| Source | Observed mechanism | Blob |
| --- | --- | --- |
| [Family compiler](../../../../../../../cs/src/gkr_compiler/family_circuit.rs) | Native execute masks PC and architectural memory products; it also masks the decoder query. | `df29400096c2e540edd28e2014ca1113a42acf8e` |
| [Contribution compiler](../../../../../../../cs/src/gkr_compiler/memory_like_grand_product.rs) | Separate raw PC/clock and port tuples; enforced masking gates on both final read/write contributions. | `6f4ae37c6c8643f5f2aac40b399502ea10699ffb` |
| [Mask kernel](../../../../../../../prover/src/gkr/sumcheck/evaluation_kernels/kernel_impls/mask_into_identity.rs) | Enforced polynomial `(input - 1) * execute + 1`. | `a9688b531bbb67476dc39b95f4953c3e21d3c03a` |
| [Generated ADD/SUB verifier](../../../../../../../verifier/src/generated/add_sub_lui_auipc_mop/sec_100/gkr.rs) | Contains both mask gates and evaluates the same polynomial. | `66633ee6e714d7c2391109a7b562a1bf5984da6e` |

[Padding regressions](../../../../../Tests/PaddingBoundary.lean) retain the
execute-zero PC 0→4/result-123 case with complete native clock lookups, reject a
padding-only forged terminal transition and non-Boolean selectors, and distinguish
identity factors from active zero values. A colliding encoding example explicitly
shows why scalar product equality is not tuple matching.
[Dependent trace](../../../../../Tests/TraceExecution.lean) inserts two such rows
into the actual initialized two-ADD execution and proves the same terminal Sail
observations. The [unissued G](../../../../../Tests/DelegationZeroInvocation.lean)
and [invalid bigint controls](../../../../../Tests/UnifiedDelegation.lean) inhabit
the new logical boundary without new participation/control assumptions.

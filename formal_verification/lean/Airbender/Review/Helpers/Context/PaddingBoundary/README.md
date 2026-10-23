# External contribution-mask boundary

[Model](Model.lean) records the enforced GKR gate and exact logical closure over
all native row occurrences. [Theorems](Theorems.lean) checks its algebra and derives
ordinary active-trace acceptance; [implementation](../../../../Proofs/PaddingBoundary.lean)
contains identity erasure and padding insertion. The user authorized this external
boundary on 15 October 2026, analogous to the
[canonical verifier-PC binding](../VerifierBoundary/README.md).

## Contract and checked result

`mask execute input = 1 + execute * (input - 1)`. At zero it is one, and at one it
preserves the input. `contribution` represents identity as `Option.none` and an entire
native tuple as `some tuple`; a zero-valued active tuple remains `some tuple`.
`product_soundness` proves that these symbolic factors agree with masking the
aggregate product for a Boolean selector. It holds for arbitrary tuple encodings
and values, without operand or result assumptions.

`Airbender.PaddingBoundary.Binding` retains the whole unfiltered layout and uses each row's actual imported
execute column. It supplies Booleanity and exact masked PC/memory permutations,
with the public initial/terminal contributions unmasked. `Airbender.PaddingBoundary.AcceptedLayout` also
checks imported constraints and every retained auxiliary/range/timestamp query
for every raw row. Active decoder membership stays in the existing public APIs;
no original instruction is required for inactive decoder padding.

`Airbender.PaddingBoundary.acceptance_soundness` erases identity factors and derives [`Airbender.Trace.Accepted`](../Model.lean) for
`active trace`. Selection preserves native occurrence order and multiplicity,
including duplicate padding rows. All public initial/terminal tokens, modeled
tables and full raw active tuples are unchanged. No inactive PC, timestamp, write
or result is required to stutter. Padding insertion is proved from execute zero
and the actual constraints, rather than assumed to preserve execution.

[Unified machine/worker binding](../../UnifiedReduced/PaddingBoundary.lean)
separately closes architectural GPR/RAM and full-width virtual CSR requests,
using the same native machine and worker selectors. All four worker layouts are
covered. Invocation clock zero is not a padding selector: raw execute-one
workers survive filtering. Current native BabyBear timestamp constraints
separately reject active zero-clock workers. Both invalid bigint controls remain admitted.
The [whole-execution entries](../../../Trace/Padding.lean) reuse restricted Sail,
six-family native boot/ROM, unified standard/TRIADD/XORROT execution and the
existing mixed caller observation certificate. Public configuration, domains,
canonical verifier-PC closure, discarded-load profiles, modeled tables, field
minima and inverses retain their existing scopes. Full custom-CSR execution and
native worker ROM transport are not added by this boundary.

## External meaning and provenance

The exact tuple permutations in `Airbender.PaddingBoundary.Binding` are external logical assumptions.
Mask algebra alone, or equal products at sampled challenges, does not imply them.
No project axiom is introduced: the theorems take the named contract as an input.
Address-space projection, binding compiled selector copies to native execute
columns, GKR/commitment/sumcheck soundness and Rust/artifact correspondence remain
external. The new boundary conditionally resolves architectural padding erasure;
it does not prove the Rust verifier implementation correct.

The current source was re-inspected on 22 October 2026 at checkout
`9683fe67d16aabadd31140a062082e79c7bccf43`, based on upstream `451884662`.
The [eight-file evidence manifest](../../../../../artifacts/setup/native-evidence.json)
records current hashes/observations and retains the earlier `4a12ba264` inspection
as historical. Identity checks do not establish Rust or cryptographic refinement.

| Source | Observed mechanism | Blob |
| --- | --- | --- |
| [Family compiler](../../../../../../../cs/src/gkr_compiler/family_circuit.rs) | Native execute masks PC and architectural memory products; it also masks the decoder query. | `708f69088d9875ad6941099950b0bbab5933a6ba` |
| [Contribution compiler](../../../../../../../cs/src/gkr_compiler/memory_like_grand_product.rs) | Separate raw PC/clock and port tuples; enforced masking gates on both final read/write contributions. | `b99efc7ee516ea085c2c42399029b10fbb93f4f1` |
| [Mask kernel](../../../../../../../prover/src/gkr/sumcheck/evaluation_kernels/kernel_impls/mask_into_identity.rs) | Enforced polynomial `(input - 1) * execute + 1`. | `a9688b531bbb67476dc39b95f4953c3e21d3c03a` |
| [Generated ADD/SUB verifier](../../../../../../../verifier/src/generated/add_sub_lui_auipc_mop/sec_100/gkr.rs) | Contains both mask gates and evaluates the same polynomial. | `1c4cc94c026b22f7a41765126881e8d554653cd3` |

[Padding regressions](../../../../../Tests/PaddingBoundary.lean) retain the
execute-zero PC 0→4/result-123 case with complete native clock lookups, reject a
padding-only forged terminal transition and non-Boolean selectors, and distinguish
identity factors from active zero values. A colliding encoding example explicitly
shows why scalar product equality is not tuple matching.
[Dependent trace](../../../../../Tests/TraceExecution.lean) inserts two such rows
into the actual initialized two-ADD execution and proves the same terminal Sail
observations. The [historical unissued G](../../../../../Tests/DelegationZeroInvocation.lean)
survives raw filtering but fails current native acceptance. The
[invalid bigint controls](../../../../../Tests/UnifiedDelegation.lean) remain
admitted without a new control assumption.

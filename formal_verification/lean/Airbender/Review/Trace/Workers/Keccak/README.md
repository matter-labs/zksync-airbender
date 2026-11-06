# Keccak worker permutations

<!-- source-names: keccak_special5 keccak_f1600 -->

The proved full unsigned machine target includes the blessed 361-call split
Keccak wrapper. The older special5 worker has a separate 649-call permutation
claim and is excluded by the three machine targets' public caller profiles.

## Checked results

| Path | Review statement | Conditions |
| --- | --- | --- |
| Split: parity, theta/rho and chi5 | [`Airbender.Keccak.Split.Native.permutation_soundness`](SplitPermutation.lean) | All 361 actual native calls, direct imported constraints, initialized histories, exact event matching, public call arguments and physical snapshots. |
| Special5 | [`Airbender.Keccak.Native.permutation_soundness`](Theorems.lean) | The complete 649-call span, modeled controller tables and the explicit worker ABI/domain profile. |

[Split schedule](SplitSchedule.lean) and [public wrapper use](SplitUse.lean)
state 24 rounds of five parity, five theta/rho and five chi5 calls, followed by
one final parity call for delayed iota. The [split native interface](SplitNative.lean)
preserves the physical ports, grouped timestamps and cached/no-cache constraints.
[Split requests](SplitRequests.lean) binds the full-width CSR, caller clock and
canonical retirement to worker fulfillments. The
[native permutation proof](../../../../Proofs/Keccak/SplitNativePermutation.lean)
connects the actual 361-call chain to Clean's original `Specs.Keccak256.keccakPermutation`.

The [full unsigned target proof](../../../../Proofs/FullUnsigned/Target.lean)
composes split worker effects, request/RAM matching, public supported use and
one standalone initialization/teardown instance. Its three source certificates
bind the original parity, theta/rho and chi5 setup rows; tagged theta/rho and chi5
queries cannot select zero padding. Final frontend, environment and independent
replay assurance remain pending as recorded in
[verification status](../../../../../VERIFICATION_STATUS.md#current-checkpoint).

The target corollaries use cached native certificates for CPU rows only.
Standard worker equations remain no-cache flat constraints, and split circuits
have no compiler capture. The full unsigned submitted worker roster is restricted
to its standard families and represented split pool. Unified/reduced omit split
pools by premise. These are instance-scope restrictions, not absence derived
merely from the program's caller registry.

## Special5 interfaces

[Theorems](Theorems.lean) proves local operation execution, complete permutation
and boundary/window results. [Reference calls](ReferenceCalls.lean) executes the
independent [micro-call reference](../../../Circuits/Keccak/Call.lean) in actual
Sail states with exact writes and frame. [Permutation](Permutation.lean) binds
the original reference to initial/final lanes; [Windows](Windows.lean) retains
seed timestamps and the first complete 649-call span.

[Full mixed execution](../../UnifiedReduced/FullExecution.lean) and
[native-path execution](../../UnifiedReduced/NativePathExecution.lean) retain
their separate supported caller and witness contracts. Complete grouped spans
also retain protocol coverage and valid memory gaps. Worker-only inputs expose
clock room and the invocation high limb; integrated caller matching derives
those bounds. Actual lane reads and pointer bounds come from initialized history.

The [known-answer regression](../../../../../Tests/KeccakKnownAnswer.lean)
compares Clean's permutation with pinned XKCP/NIST vectors. This finite check is
separate from the universal split and special5 worker theorems.

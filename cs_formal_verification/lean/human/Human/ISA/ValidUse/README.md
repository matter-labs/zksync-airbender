# Valid delegation use

[Model.lean](Model.lean) defines buffer bounds, alignment and controls for bigint, BLAKE2s and Keccak
reference use, and the bigint and G reference functions. [Theorems.lean](Theorems.lean) and
[DelegationRuns.lean](../DelegationRuns.lean) define the complete call schedules. The BLAKE2s compression
reference is in [DelegationRuns.lean](../DelegationRuns.lean), and the Keccak permutation is in
[Keccak.lean](../Keccak.lean).
[Theorems.lean](Theorems.lean) states the reference claims and a separate witness
claim for each set of premises.

The reference claims connect complete valid schedules to their mathematical
results. Machine execution and caller coverage are separate claims.
Read the exact premises with the call effects of the
[delegation specification](../Delegations.lean). The kernel checks the proofs;
the reference definitions and stated interfaces are part of the reviewed spec.

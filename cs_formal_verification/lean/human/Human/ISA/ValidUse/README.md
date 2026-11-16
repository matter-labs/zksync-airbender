# Valid delegation use

[Model.lean](Model.lean) defines buffer bounds, alignment, controls and complete
call schedules for bigint, BLAKE2s and Keccak reference use.
[Theorems.lean](Theorems.lean) states the reference claims and a separate witness
claim for each set of premises.

The reference claims connect complete valid schedules to their mathematical
results. Machine execution and caller coverage are separate claims.
Read the exact premises and reference functions with the
[delegation specification](../Delegations.lean). The kernel checks the proofs;
the reference definitions and stated interfaces are part of the reviewed spec.

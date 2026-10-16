import Airbender.Review.Trace.Delegation.Theorems
import Airbender.Proofs.BabyBear

set_option Elab.async false

namespace Tests.DelegationTimestamps
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def clockRow (first ports invocation previous column : Nat) : ZMod babyBearModulus :=
  if column = 1 then invocation
  else if first ≤ column ∧ column < first + 3 * ports then
    if (column - first) % 3 = 0 then previous
    else if (column - first) % 3 = 2 then 1 else 0
  else 0

private theorem keccak_queries (clock : Fin 2) :
    FlatOperation.ConstraintsHoldFlat
      (Verification.environment (clockRow 222 14 (if clock = 0 then 4 else 524284) 0))
      (Keccak.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  simp only [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Keccak.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 30 := by simpa only [Keccak.timestamp_count] using hi
    interval_cases i <;> fin_cases clock
    all_goals apply Trace.Proofs.range_contains
    all_goals norm_num [Keccak.importedConstraintsTimestampLookups, FlatOperation.lookups,
      Expression.eval, Verification.environment, clockRow, Trace.timestampBase,
      ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]

private theorem bigint_queries :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (clockRow 217 19 4 0))
      (Bigint.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  simp only [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 40 := by simpa only [Bigint.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals norm_num [Bigint.importedConstraintsTimestampLookups, FlatOperation.lookups,
      Expression.eval, Verification.environment, clockRow, Trace.timestampBase,
      ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]

private theorem blakeG_queries :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (clockRow 83 9 4 0))
      (Blake2G.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  simp only [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Blake2G.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 20 := by simpa only [Blake2G.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals norm_num [Blake2G.importedConstraintsTimestampLookups, FlatOperation.lookups,
      Expression.eval, Verification.environment, clockRow, Trace.timestampBase,
      ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]

private theorem blakeRound_queries :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (clockRow 740 43 4 0))
      (Blake2Round.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  simp only [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Blake2Round.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 88 := by simpa only [Blake2Round.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals norm_num [Blake2Round.importedConstraintsTimestampLookups, FlatOperation.lookups,
      Expression.eval, Verification.environment, clockRow, Trace.timestampBase,
      ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]

theorem nativeQueries :
    (∀ clock : Fin 2, FlatOperation.ConstraintsHoldFlat
      (Verification.environment (clockRow 222 14 (if clock = 0 then 4 else 524284) 0))
      Keccak.importedConstraintsTimestampLookups) ∧
    FlatOperation.ConstraintsHoldFlat (Verification.environment (clockRow 217 19 4 0))
      Bigint.importedConstraintsTimestampLookups ∧
    FlatOperation.ConstraintsHoldFlat (Verification.environment (clockRow 83 9 4 0))
      Blake2G.importedConstraintsTimestampLookups ∧
    FlatOperation.ConstraintsHoldFlat (Verification.environment (clockRow 740 43 4 0))
      Blake2Round.importedConstraintsTimestampLookups :=
  ⟨keccak_queries, bigint_queries, blakeG_queries, blakeRound_queries⟩

theorem nonadvancingAccessRejected :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment (clockRow 222 14 4 6))
      (Keccak.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  intro h
  have lower := Trace.Proofs.range_bound (Verification.lookup_of_holds h
    ⟨2, by rw [Keccak.timestamp_count]; decide⟩)
  norm_num [Keccak.importedConstraintsTimestampLookups, FlatOperation.lookups,
    Expression.eval, Verification.environment, clockRow, Trace.timestampBase,
    ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus] at lower

theorem invalidInvocationRejected :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment (clockRow 222 14 524288 0))
      (Keccak.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  intro h
  have lower := Trace.Proofs.range_bound (Verification.lookup_of_holds h
    ⟨0, by rw [Keccak.timestamp_count]; decide⟩)
  norm_num [Keccak.importedConstraintsTimestampLookups, FlatOperation.lookups,
    Expression.eval, Verification.environment, clockRow, Trace.timestampBase,
    ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus] at lower

end Tests.DelegationTimestamps

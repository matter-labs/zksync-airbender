import Airbender.Review.Circuits.ReducedMachine.PhysicalScalar16Setup
import Airbender.Proofs.Tables.NativeScalars
import Airbender.Proofs.Tables.NormalizeLast
import Airbender.Proofs.ReducedMachine.NativeScalar16Arguments

namespace Airbender.NativePhysicalScalar16SetupProofs
open Airbender.NativePhysicalScalar16Setup Airbender.NativeScalar16Arguments Airbender.ReducedMachine.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem geometry : scalar16Layout.traceLength = 8388608 ∧ scalar16Layout.setup.index = 0 ∧
    Verification.NativeSetup.ScalarKind.range16.data.length = 65536 := by decide +kernel

theorem ordinary_value (i : Nat) : ordinaryValue i = if i < 65536 then (i : F) else 0 := by
  unfold ordinaryValue
  by_cases present : i < Verification.NativeSetup.ScalarKind.range16.data.length
  · have literal := Verification.NativeSetup.Proofs.exported_scalar_rows .range16 ⟨i,present⟩
    have small : i < 65536 := present
    rw [dif_pos present,if_pos small]
    simp [Setup.TableData.row,literal]
  · have absent : ¬ i < 65536 := present
    rw [dif_neg present,if_neg absent]

theorem ordinary_tail (i : Nat) (tail : 65536 ≤ i) : ordinaryValue i = 0 := by
  rw [ordinary_value,if_neg (by omega)]

private theorem sum_double {R : Type} [CommRing R] (size : Nat) :
    (2 : R)*(∑ i ∈ Finset.range size,(i : R)) = (size : R)*((size : R)-1) := by
  induction size with
  | zero => simp
  | succ size ih =>
    rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
    linear_combination ih

private theorem padded_double {R : Type} [CommRing R] (rows : Nat → R) (cutoff size : Nat)
    (fits : cutoff ≤ size) (head : ∀ i < cutoff, rows i = (i : R))
    (tail : ∀ i, cutoff ≤ i → rows i = 0) :
    (2 : R)*(∑ i ∈ Finset.range size,rows i) = (cutoff : R)*((cutoff : R)-1) := by
  have support : (∑ i ∈ Finset.range cutoff,rows i) = ∑ i ∈ Finset.range size,rows i := by
    apply Finset.sum_subset (Finset.range_mono fits)
    intro i _ outside
    exact tail i (Nat.le_of_not_lt (fun h => outside (Finset.mem_range.mpr h)))
  rw [← support]
  have prefixValues : (∑ i ∈ Finset.range cutoff,rows i) = ∑ i ∈ Finset.range cutoff,(i : R) := by
    apply Finset.sum_congr rfl
    intro i member
    exact head i (Finset.mem_range.mp member)
  rw [prefixValues]
  exact sum_double cutoff

theorem ordinary_sum : (∑ i ∈ Finset.range (scalar16Layout.traceLength-1),ordinaryValue i) = (2147450880 : F) := by
  have h := padded_double (R := F) ordinaryValue 65536 (scalar16Layout.traceLength-1) (by decide)
    (fun i small => by rw [ordinary_value,if_pos small]) ordinary_tail
  have two : (2 : F) ≠ 0 := by decide +kernel
  have constant : (65536 : F)*(65536-1) = 2*(2147450880 : F) := by decide +kernel
  exact mul_left_cancel₀ two (h.trans constant)

private theorem normalized_reference_generic {R : Type} [AddCommGroup R] (size : Nat) (rows : Nat → R)
    (total : R) (summed : (∑ i ∈ Finset.range (size-1),rows i) = total) (i : Nat) :
    Verification.normalizeLast size rows i = if i = size-1 then -total else rows i := by
  unfold Verification.normalizeLast
  rw [summed]

theorem normalized_reference (i : Nat) :
    Verification.normalizeLast scalar16Layout.traceLength ordinaryValue i = normalizedValue i := by
  have h := normalized_reference_generic scalar16Layout.traceLength ordinaryValue (2147450880 : F) ordinary_sum i
  have adjustment : -(2147450880 : F) = 32767 := by decide +kernel
  simpa only [adjustment,normalizedValue] using h

theorem normalized_ordinary (i : Nat) (ordinary : i < scalar16Layout.traceLength-1) :
    normalizedValue i = ordinaryValue i := if_neg (Nat.ne_of_lt ordinary)

theorem normalized_terminal : normalizedValue (scalar16Layout.traceLength-1) = 32767 := if_pos rfl

theorem normalized_sum : (∑ i ∈ Finset.range scalar16Layout.traceLength,normalizedValue i) = 0 := by
  have h := Verification.NormalizeLastProofs.domain_sum (R := F) (size := scalar16Layout.traceLength) (by decide) ordinaryValue
  simpa only [normalized_reference] using h

theorem bound_initialization {R : Type} [Field R] (proof : Proof R) :
    (withPublicSetup proof).initialization = proof.initialization := rfl

theorem bound_setup {R : Type} [Field R] (proof : Proof R) (i : Nat) :
    (withPublicSetup proof).setup i scalar16Layout.setup = normalizedValue i := by
  simp only [withPublicSetup,ite_true]

theorem constructed_ordinary {R : Type} [Field R] (proof : Proof R) (i : Nat)
    (ordinary : i < scalar16Layout.traceLength-1) :
    (withPublicSetup proof).setup i scalar16Layout.setup = ordinaryValue i :=
  (bound_setup proof i).trans (normalized_ordinary i ordinary)

theorem bound_other_setup {R : Type} [Field R] (proof : Proof R) (i : Nat) (column : Scalar16SetupColumn)
    (other : column.index ≠ scalar16Layout.setup.index) :
    (withPublicSetup proof).setup i column = proof.setup i column := if_neg other

/-- Literal prefix plus actual zero tail yields canonical range membership;
    this is a theorem about the CONSTRUCTED table, not an equivalence premise. -/
theorem membership (value : F) : table.Contains #[] #v[value] ↔ value.val < 65536 := by
  change (∃ i : Fin (scalar16Layout.traceLength-1), #v[value] = #v[ordinaryValue i.val]) ↔ value.val < 65536
  constructor
  · rintro ⟨i,same⟩
    have sameValue : value = ordinaryValue i.val := by
      simpa using congrArg (fun query : Vector F 1 => query[0]) same
    rw [ordinary_value] at sameValue
    split_ifs at sameValue with present
    · rw [sameValue,ZMod.val_natCast]
      exact lt_of_le_of_lt (Nat.mod_le _ _) present
    · rw [sameValue,ZMod.val_zero]
      decide
  · intro small
    refine ⟨⟨value.val,by change value.val < 8388607; omega⟩,?_⟩
    rw [ordinary_value,if_pos small,ZMod.natCast_zmod_val]
end Airbender.NativePhysicalScalar16SetupProofs

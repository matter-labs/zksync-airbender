import Airbender.Review.Keccak.Theorems
import Airbender.Proofs.BabyBear
import Mathlib.Tactic.IntervalCases

namespace Tests.KeccakMix
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4800000

private def parities : Vector Nat 5 :=
  #v[0xffffffffffffffff, 0x0123456789abcdef, 0x8080808080808080,
    0xaaaaaaaaaaaaaaaa, 0x5555555555555555]
private def rotated (i : Fin 5) : Nat := rotLeft64 parities[i] 1
private def firstWrites : Vector Nat 6 :=
  #v[parities[0] ^^^ rotated 2, parities[1], parities[2] ^^^ rotated 4,
    parities[3], parities[4], rotated 0]
private def reads (second : Bool) : Vector Nat 6 :=
  if second then firstWrites else #v[parities[0], parities[1], parities[2], parities[3], parities[4], 0]
private def writes (second : Bool) : Vector Nat 6 :=
  if second then
    #v[firstWrites[0], parities[1] ^^^ rotated 3, firstWrites[2], parities[3] ^^^ rotated 0,
      parities[4] ^^^ rotated 1, rotated 0]
  else firstWrites
private def temps (second : Bool) : Vector Nat 3 :=
  if second then #v[rotated 1, rotated 3, 0] else #v[rotated 2, rotated 4, 0]
private def aWords (second : Bool) : Vector Nat 5 :=
  if second then #v[parities[1], parities[4], parities[3], parities[1], parities[3]]
  else #v[parities[0], parities[2], parities[0], parities[4], parities[2]]
private def bWords (second : Bool) : Vector Nat 5 :=
  if second then #v[0, rotated 1, 0, rotated 3, rotated 0]
  else #v[0, 0, rotated 2, 0, rotated 4]
private def cWords (second : Bool) : Vector Nat 5 :=
  if second then #v[rotated 1, (writes true)[4], rotated 3, (writes true)[1], (writes true)[3]]
  else #v[rotated 0, rotated 2, firstWrites[0], rotated 4, firstWrites[2]]
private def rotation (second : Bool) (op : Fin 5) : Bool :=
  if second then op.val = 0 || op.val = 2 else op.val = 0 || op.val = 1 || op.val = 3
private def control (_ : Fin 4096) : Vector Nat 6 := #v[0, 5, 10, 15, 20, 25]
private abbrev setup : Table (ZMod babyBearModulus) (fields 8) := Keccak.setupTable control
private def stateControl (second : Bool) : Keccak.ControlState := ⟨if second then 2 else 1, 0, 24⟩

private def row (second : Bool) (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 70 ∨ v = (if second then 65 else 64) then 1
  else if v = 3 then (stateControl second).packed
  else if v = 5 then (stateControl second).nextPacked
  else if 7 ≤ v ∧ v < 13 then (5 * (v - 7) : Nat)
  else if h : 15 ≤ v ∧ v < 63 then
    let lane : Fin 6 := ⟨(v - 15) / 8, by omega⟩
    let limb := ((v - 15) % 8) / 4 * 2 + (v - 15) % 2
    let value := if (v - 15) % 4 < 2 then (reads second)[lane] else (writes second)[lane]
    (value / 2 ^ (16 * limb) % 65536 : Nat)
  else if 75 ≤ v ∧ v < 80 then (24 / 2 ^ (v - 75) % 2 : Nat)
  else if v = 85 then 24
  else if 86 ≤ v ∧ v < 90 then (14360 + 16448 * (v - 86) : Nat)
  else if h : 90 ≤ v ∧ v < 102 then
    let temporary : Fin 3 := ⟨(v - 90) / 4, by omega⟩
    ((temps second)[temporary] / 2 ^ (16 * ((v - 90) % 4)) % 65536 : Nat)
  else if h : 102 ≤ v ∧ v < 222 then
    let op : Fin 5 := ⟨(v - 102) / 24, by omega⟩
    let column := ((v - 102) % 24) / 8
    let slot := (v - 102) % 8
    if rotation second op then
      if slot < 4 then
        let limb := (aWords second)[op] / 2 ^ (16 * slot) % 65536
        if column = 0 then (limb + 65536 : Nat)
        else if column = 1 then (limb / 32768 : Nat) else (2 * limb % 65536 : Nat)
      else 0
    else
      let value := if column = 0 then (aWords second)[op]
        else if column = 1 then (bWords second)[op] else (cWords second)[op]
      (value / 2 ^ (8 * slot) % 256 : Nat)
  else 0

private def byteIndex (second : Bool) (i : Fin 40) : Nat :=
  let op : Fin 5 := ⟨i.val / 8, by omega⟩
  if rotation second op then
    200705 + if i.val % 8 < 4 then (aWords second)[op] / 2 ^ (16 * (i.val % 8)) % 65536 + 65536 else 0
  else
    1 + 256 * ((aWords second)[op] / 2 ^ (8 * (i.val % 8)) % 256) +
      ((bWords second)[op] / 2 ^ (8 * (i.val % 8)) % 256)
private theorem byteIndexBound (second : Bool) (i : Fin 40) : byteIndex second i < 1249281 := by
  cases second <;> fin_cases i <;> decide
private theorem byteValues (second : Bool) (i : Fin 40) :
    (Keccak.Proofs.byteEntry setup i).map (Expression.eval (Verification.environment (row second))) =
      (Keccak.setupRow control ⟨byteIndex second i, byteIndexBound second i⟩).map
        (fun (n : Nat) => (n : ZMod babyBearModulus)) := by
  cases second <;> fin_cases i <;>
    dsimp [Keccak.Proofs.byteEntry, Keccak.Proofs.byteQuery, Keccak.importedConstraints, FlatOperation.lookups]
  all_goals
    apply Vector.ext
    intro j hj
    change j < 8 at hj
    interval_cases j <;> simp only [Vector.getElem_map, Vector.getElem_cast] <;> decide +kernel +revert
private theorem bytesHold (second : Bool) (i : Fin 40) :
    (Keccak.Proofs.byteQuery setup i).Contains (Verification.environment (row second)) := by
  rw [Keccak.Proofs.byte_query_shape]
  exact ⟨⟨byteIndex second i, byteIndexBound second i⟩, byteValues second i⟩
private theorem controllerHolds (second : Bool) :
    ((FlatOperation.lookups (Keccak.importedConstraints setup)).get
      ⟨1, by rw [Keccak.lookup_count]; decide⟩).Contains (Verification.environment (row second)) := by
  change ∃ index : Fin 1249281,
    ((FlatOperation.lookups (Keccak.importedConstraints setup))[1]).entry.map
      (Expression.eval (Verification.environment (row second))) =
      (Keccak.setupRow control index).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨⟨65537 + 2048 + (stateControl second).packed, by cases second <;> decide⟩, ?_⟩
  cases second <;> dsimp [Keccak.importedConstraints, FlatOperation.lookups]
  all_goals
    apply Vector.ext
    intro j hj
    change j < 8 at hj
    interval_cases j <;> simp only [Vector.getElem_map] <;> decide +kernel +revert

theorem satisfies (second : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row second))
      (Keccak.importedConstraints setup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · cases second <;> decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 42 := by simpa only [Keccak.lookup_count] using hi
    by_cases range : i = 0
    · subst i
      apply Verification.range16_contains
      cases second <;> decide
    by_cases controller : i = 1
    · subst i
      simpa only [List.get_eq_getElem] using controllerHolds second
    have relation := bytesHold second ⟨i - 2, by omega⟩
    have index : i - 2 + 2 = i := by omega
    simpa only [Keccak.Proofs.byteQuery, List.get_eq_getElem, Fin.val_mk, index] using relation

theorem nativeMapping : Keccak.MixMapping parities 24 (row false) (row true) := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · intro i; fin_cases i <;> decide
  · intro i
    apply Vector.ext
    intro j hj
    change j < 4 at hj
    fin_cases i <;> interval_cases j <;> decide +kernel +revert

theorem referenceColumns : Keccak.MixResult parities (row false) (row true) :=
  Keccak.mix_columns_soundness (by decide) (satisfies false) (satisfies true) nativeMapping

private theorem expected_nonzero : (Specs.Keccak256.thetaD parities)[0] ≠ 0 := by decide

theorem wrongWriteRejected {first second : Nat → ZMod babyBearModulus}
    (mapping : Keccak.MixMapping parities 24 first second)
    (wrong : Keccak.writeLane second 4 = 0)
    (firstHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment first) (Keccak.importedConstraints setup)) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment second) (Keccak.importedConstraints setup) := by
  intro secondHolds
  have result := (Keccak.mix_columns_soundness (by decide) firstHolds secondHolds mapping).1
  have value := congrArg (fun v : Vector Nat 5 => v[0]) result
  change Keccak.writeLane second 4 = (Specs.Keccak256.thetaD parities)[0] at value
  rw [wrong] at value
  exact expected_nonzero value.symm

end Tests.KeccakMix

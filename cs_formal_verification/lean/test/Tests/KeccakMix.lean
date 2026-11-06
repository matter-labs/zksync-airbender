import Slop.Keccak.Claims
import Slop.BabyBear
import Mathlib.Tactic.IntervalCases
import Slop.Keccak.Completeness.Bytes

namespace Tests.KeccakMix
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

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
private def rotation (second : Bool) (op : Fin 5) : Bool :=
  if second then op.val = 0 || op.val = 2 else op.val = 0 || op.val = 1 || op.val = 3
private def control (_ : Fin 4096) : Vector Nat 6 := #v[0, 5, 10, 15, 20, 25]
private abbrev setup : Table (ZMod babyBearModulus) (fields 8) := Keccak.setupTable control
private def stateControl (second : Bool) : Keccak.ControlState := ⟨if second then 2 else 1, 0, 24⟩

private def base (second : Bool) (v : Nat) : ZMod babyBearModulus :=
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
  else 0

-- Byte query `i` (operation `i / 8`, byte `i % 8`): rotation by one of a word's 16-bit limbs,
-- or the XOR bytes of two words.
private def bytes (second : Bool) (part : Fin 3) (i : Fin 40) : Nat :=
  let op : Fin 5 := ⟨i.val / 8, by omega⟩
  if rotation second op then
    if i.val % 8 < 4 then
      let limb := (aWords second)[op] / 2 ^ (16 * (i.val % 8)) % 65536
      if part.val = 0 then limb + 65536 * 1
      else if part.val = 1 then limb / 2 ^ (16 - 1) else limb * 2 ^ 1 % 65536
    else 0
  else Keccak.Proofs.wordByte (if part.val = 0 then (aWords second)[op]
    else if part.val = 1 then (bWords second)[op] else (aWords second)[op] ^^^ (bWords second)[op])
    (i.val % 8)

private def row (second : Bool) : Nat → ZMod babyBearModulus :=
  Keccak.Proofs.bytesRow (base second) (bytes second)

private theorem modes (second : Bool) (j : Fin 7) :
    row second Keccak.Variables.modeColumns[j] = if j = (if second then 2 else 1) then 1 else 0 := by
  cases second <;> fin_cases j <;> decide

private theorem mix_tags (second : Bool) (op : Fin 5) :
    Keccak.Proofs.operationTag (if second then 2 else 1) op = if rotation second op then 40 else 4 := by
  cases second <;> revert op <;> decide

private theorem bytesHold (second : Bool) (i : Fin 40) :
    (Keccak.Proofs.byteQuery setup i).Contains (Verification.environment (row second)) := by
  have tag := Keccak.Proofs.byte_tag_of_mode setup _ (modes second) i
  have byte (part : Fin 3) : row second (Keccak.Proofs.byteColumn part i) =
      (bytes second part i : Nat) := Keccak.Proofs.bytes_row_byte _ _ part i
  rw [mix_tags] at tag
  by_cases rotated : rotation second ⟨i.val / 8, by omega⟩
  · rw [ite_eq_left rotated] at tag
    by_cases low : i.val % 8 < 4
    · refine Keccak.Proofs.rotation_query i
        (Nat.mod_lt ((aWords second)[(⟨i.val / 8, by omega⟩ : Fin 5)] / 2 ^ (16 * (i.val % 8))) (by decide))
        (by decide : 1 < 16) ?_ ?_ ?_ tag
      all_goals rw [byte]; simp only [bytes, rotated, low, ↓reduceIte, Fin.isValue]; rfl
    · refine Keccak.Proofs.rotation_zero_query i ?_ ?_ ?_ tag
      all_goals rw [byte]; simp only [bytes, rotated, low, ↓reduceIte, Nat.cast_zero]
  · rw [ite_eq_right rotated] at tag
    refine Keccak.Proofs.xor_query i (aWords second)[(⟨i.val / 8, by omega⟩ : Fin 5)]
      (bWords second)[(⟨i.val / 8, by omega⟩ : Fin 5)] ?_ ?_ ?_ tag
    all_goals rw [byte]; simp only [bytes, rotated, ↓reduceIte, Fin.isValue, Bool.false_eq_true]; rfl

private theorem controllerHolds (second : Bool) :
    ((FlatOperation.lookups (Keccak.importedConstraints setup)).get
      ⟨1, by rw [Keccak.lookup_count]; decide⟩).Contains (Verification.environment (row second)) := by
  refine Keccak.Proofs.controller_query (key := 2048 + (stateControl second).packed) (by cases second <;> decide) ?_ ?_
  · cases second <;> decide
  · cases second <;> decide

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
      apply Trace.Proofs.range_contains
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

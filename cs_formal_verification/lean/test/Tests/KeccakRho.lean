import Slop.Keccak.Claims
import Slop.BabyBear
import Mathlib.Tactic.IntervalCases
import Slop.Keccak.Completeness.Bytes

namespace Tests.KeccakRho
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6400000

private def scratch : Nat := 0x0100000000000001
private def initial : Nat := 0xffffffffffffffff
private def mixed : Nat := initial ^^^ scratch
private def state : Vector Nat 25 := Vector.replicate 25 initial
private def d : Vector Nat 5 := Vector.replicate 5 scratch
private def control (_ : Fin 4096) : Vector Nat 6 := #v[0, 5, 10, 15, 20, 25]
private abbrev setup : Table (ZMod babyBearModulus) (fields 8) := Keccak.setupTable control
private def stateControl (rho : Bool) (column : Fin 5) : Keccak.ControlState :=
  ⟨if rho then 4 else 3, column, 0⟩
private def rotation (column op : Fin 5) : Fin 64 := Keccak.Proofs.Rho.rotations[column][op]
private def value (rho write : Bool) (column : Fin 5) (lane : Fin 6) : Nat :=
  if h : lane.val < 5 then
    if rho then if write then rotLeft64 mixed (rotation column ⟨lane.val, h⟩) else mixed
    else if write then mixed else initial
  else scratch

private def base (rho : Bool) (column : Fin 5) (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 70 + column.val ∨ v = (if rho then 67 else 66) then 1
  else if v = 3 then (stateControl rho column).packed
  else if v = 5 then (stateControl rho column).nextPacked
  else if 7 ≤ v ∧ v < 13 then (5 * (v - 7) : Nat)
  else if h : 15 ≤ v ∧ v < 63 then
    let lane : Fin 6 := ⟨(v - 15) / 8, by omega⟩
    let limb := ((v - 15) % 8) / 4 * 2 + (v - 15) % 2
    (value rho ((v - 15) % 4 ≥ 2) column lane / 2 ^ (16 * limb) % 65536 : Nat)
  else if rho ∧ v = 80 + column.val then 1
  else if 86 ≤ v ∧ v < 90 then (8192 + 16448 * (v - 86) : Nat)
  else 0

-- Byte query `i` (operation `i / 8`, byte `i % 8`): rotation pieces of the mixed lane's limbs
-- in Rho mode, the XOR bytes of the two Theta inputs otherwise.
private def bytes (rho : Bool) (column : Fin 5) (part : Fin 3) (i : Fin 40) : Nat :=
  let op : Fin 5 := ⟨i.val / 8, by omega⟩
  if rho then
    if i.val % 8 < 4 then
      let limb := mixed / 2 ^ (16 * (i.val % 8)) % 65536
      let shift := (rotation column op).val % 16
      if part.val = 0 then limb + 65536 * shift
      else if part.val = 1 then limb / 2 ^ (16 - shift) else limb * 2 ^ shift % 65536
    else 0
  else Keccak.Proofs.wordByte (if part.val = 0 then initial else if part.val = 1 then scratch else mixed)
    (i.val % 8)

private def row (rho : Bool) (column : Fin 5) : Nat → ZMod babyBearModulus :=
  Keccak.Proofs.bytesRow (base rho column) (bytes rho column)

private theorem modes (rho : Bool) (column : Fin 5) (j : Fin 7) :
    row rho column Keccak.Variables.modeColumns[j] = if j = (if rho then 4 else 3) then 1 else 0 := by
  cases rho <;> fin_cases column <;> fin_cases j <;> decide

private theorem bytesHold (rho : Bool) (column : Fin 5) (i : Fin 40) :
    (Keccak.Proofs.byteQuery setup i).Contains (Verification.environment (row rho column)) := by
  have tag := Keccak.Proofs.byte_tag_of_mode setup _ (modes rho column) i
  have byte (part : Fin 3) : row rho column (Keccak.Proofs.byteColumn part i) =
      (bytes rho column part i : Nat) := Keccak.Proofs.bytes_row_byte _ _ part i
  cases rho
  · have xor : ∀ op : Fin 5, Keccak.Proofs.operationTag 3 op = 4 := by decide
    simp only [Bool.false_eq_true, ↓reduceIte] at tag
    rw [xor] at tag
    exact Keccak.Proofs.xor_query i initial scratch (byte 0) (byte 1) (byte 2) tag
  · have rotate : ∀ op : Fin 5, Keccak.Proofs.operationTag 4 op = 40 := by decide
    simp only [↓reduceIte] at tag
    rw [rotate] at tag
    by_cases slot : i.val % 8 < 4
    · refine Keccak.Proofs.rotation_query i (Nat.mod_lt (mixed / 2 ^ (16 * (i.val % 8))) (by decide))
        (Nat.mod_lt (rotation column ⟨i.val / 8, by omega⟩).val (by decide)) ?_ ?_ ?_ tag
      all_goals rw [byte]; simp only [bytes, slot, ↓reduceIte, Fin.isValue]; rfl
    · refine Keccak.Proofs.rotation_zero_query i ?_ ?_ ?_ tag
      all_goals rw [byte]; simp only [bytes, slot, ↓reduceIte, Nat.cast_zero]

private theorem controllerHolds (rho : Bool) (column : Fin 5) :
    ((FlatOperation.lookups (Keccak.importedConstraints setup)).get
      ⟨1, by rw [Keccak.lookup_count]; decide⟩).Contains (Verification.environment (row rho column)) := by
  refine Keccak.Proofs.controller_query (key := 2048 + (stateControl rho column).packed) (by cases rho <;> fin_cases column <;> decide) ?_ ?_
  · cases rho <;> fin_cases column <;> decide
  · cases rho <;> fin_cases column <;> decide

theorem satisfies (rho : Bool) (column : Fin 5) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row rho column))
      (Keccak.importedConstraints setup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · cases rho <;> fin_cases column <;> decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 42 := by simpa only [Keccak.lookup_count] using hi
    by_cases range : i = 0
    · subst i
      apply Verification.range16_contains
      cases rho <;> fin_cases column <;> decide
    by_cases controller : i = 1
    · subst i
      simpa only [List.get_eq_getElem] using controllerHolds rho column
    have relation := bytesHold rho column ⟨i - 2, by omega⟩
    have index : i - 2 + 2 = i := by omega
    simpa only [Keccak.Proofs.byteQuery, List.get_eq_getElem, Fin.val_mk, index] using relation

theorem nativeMapping (column : Fin 5) :
    Keccak.ThetaRhoMapping state d column 0 (row false column) (row true column) := by
  constructor
  · fin_cases column <;> decide
  · fin_cases column <;> decide
  · fin_cases column <;> decide
  · fin_cases column <;> decide
  · intro i; fin_cases column <;> fin_cases i <;> decide
  · fin_cases column <;> decide
  · intro i
    apply Vector.ext
    intro j hj
    change j < 4 at hj
    fin_cases column <;> fin_cases i <;> interval_cases j <;> decide +kernel +revert

theorem referenceColumns (column : Fin 5) : Keccak.RhoResult state d column (row true column) :=
  Keccak.theta_rho_column_soundness (by decide) (satisfies false column)
    (satisfies true column) (nativeMapping column)

private theorem expected_nonzero (column : Fin 5) :
    (Specs.Keccak256.rhoPi (Specs.Keccak256.thetaXor state d))[Keccak.rhoDestinations[column][0]] ≠ 0 := by
  fin_cases column <;> decide

theorem wrongWriteRejected {theta rho : Nat → ZMod babyBearModulus} {column : Fin 5}
    (mapping : Keccak.ThetaRhoMapping state d column 0 theta rho)
    (wrong : Keccak.writeLane rho 0 = 0)
    (thetaHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment theta)
      (Keccak.importedConstraints setup)) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment rho) (Keccak.importedConstraints setup) := by
  intro rhoHolds
  have value := (Keccak.theta_rho_column_soundness (by decide) thetaHolds rhoHolds mapping).1 (0 : Fin 5)
  change Keccak.writeLane rho 0 = _ at value
  rw [wrong] at value
  exact expected_nonzero column value.symm

end Tests.KeccakRho

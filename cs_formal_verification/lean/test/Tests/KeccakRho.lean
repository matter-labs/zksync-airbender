import Slop.Keccak.Claims
import Slop.BabyBear
import Mathlib.Tactic.IntervalCases

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

private def row (rho : Bool) (column : Fin 5) (v : Nat) : ZMod babyBearModulus :=
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
  else if h : 102 ≤ v ∧ v < 222 then
    let op : Fin 5 := ⟨(v - 102) / 24, by omega⟩
    let part := ((v - 102) % 24) / 8
    let slot := (v - 102) % 8
    if rho then
      if slot < 4 then
        let limb := mixed / 2 ^ (16 * slot) % 65536
        let shift := (rotation column op).val % 16
        if part = 0 then (limb + 65536 * shift : Nat)
        else if part = 1 then (limb / 2 ^ (16 - shift) : Nat)
        else (limb * 2 ^ shift % 65536 : Nat)
      else 0
    else
      let word := if part = 0 then initial else if part = 1 then scratch else mixed
      (word / 2 ^ (8 * slot) % 256 : Nat)
  else 0

private def byteIndex (rho : Bool) (column : Fin 5) (i : Fin 40) : Nat :=
  let op : Fin 5 := ⟨i.val / 8, by omega⟩
  if rho then 200705 + if i.val % 8 < 4 then
    mixed / 2 ^ (16 * (i.val % 8)) % 65536 + 65536 * ((rotation column op).val % 16) else 0
  else 1 + 256 * (initial / 2 ^ (8 * (i.val % 8)) % 256) +
    (scratch / 2 ^ (8 * (i.val % 8)) % 256)
private theorem byteIndexBound (rho : Bool) (column : Fin 5) (i : Fin 40) :
    byteIndex rho column i < 1249281 := by
  cases rho <;> fin_cases column <;> fin_cases i <;> decide
private theorem byteValues (rho : Bool) (column : Fin 5) (i : Fin 40) :
    (Keccak.Proofs.byteEntry setup i).map (Expression.eval (Verification.environment (row rho column))) =
      (Keccak.setupRow control ⟨byteIndex rho column i, byteIndexBound rho column i⟩).map
        (fun (n : Nat) => (n : ZMod babyBearModulus)) := by
  cases rho <;> fin_cases column <;> fin_cases i <;>
    dsimp [Keccak.Proofs.byteEntry, Keccak.Proofs.byteQuery, Keccak.importedConstraints, FlatOperation.lookups]
  all_goals
    apply Vector.ext
    intro j hj
    change j < 8 at hj
    interval_cases j <;> simp only [Vector.getElem_map, Vector.getElem_cast] <;> decide +kernel +revert
private theorem bytesHold (rho : Bool) (column : Fin 5) (i : Fin 40) :
    (Keccak.Proofs.byteQuery setup i).Contains (Verification.environment (row rho column)) := by
  rw [Keccak.Proofs.byte_query_shape]
  exact ⟨⟨byteIndex rho column i, byteIndexBound rho column i⟩, byteValues rho column i⟩
private theorem controllerHolds (rho : Bool) (column : Fin 5) :
    ((FlatOperation.lookups (Keccak.importedConstraints setup)).get
      ⟨1, by rw [Keccak.lookup_count]; decide⟩).Contains (Verification.environment (row rho column)) := by
  change ∃ index : Fin 1249281,
    ((FlatOperation.lookups (Keccak.importedConstraints setup))[1]).entry.map
      (Expression.eval (Verification.environment (row rho column))) =
      (Keccak.setupRow control index).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨⟨65537 + 2048 + (stateControl rho column).packed, by
    cases rho <;> fin_cases column <;> decide⟩, ?_⟩
  cases rho <;> fin_cases column <;> dsimp [Keccak.importedConstraints, FlatOperation.lookups]
  all_goals
    apply Vector.ext
    intro j hj
    change j < 8 at hj
    interval_cases j <;> simp only [Vector.getElem_map] <;> decide +kernel +revert

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

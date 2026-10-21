import Airbender.Proofs.Keccak.Claims
import Airbender.Proofs.BabyBear
import Mathlib.Tactic.IntervalCases

set_option Elab.async false

namespace Tests.KeccakIota
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 9600000

private def referenceState : Vector Nat 25 := Vector.ofFn fun i =>
  (#v[0xffffffffffffffff, 0x0123456789abcdef, 0x8080808080808080,
    0xaaaaaaaaaaaaaaaa, 0x5555555555555555] : Vector Nat 5)[i.val % 5]
private def selectedColumn (case : Fin 3) : Fin 5 := if case.val = 2 then 2 else 0
private def selectedRound (case : Fin 3) : Fin 25 := if case.val = 0 then 0 else 24
private def effectiveRound (case : Fin 3) : Nat :=
  if (selectedColumn case).val = 0 then (selectedRound case).val else 0
private def stateControl (case : Fin 3) : Keccak.ControlState :=
  ⟨0, selectedColumn case, ⟨(selectedRound case).val, by have := (selectedRound case).isLt; omega⟩⟩
private def control (_ : Fin 4096) : Vector Nat 6 := #v[0, 5, 10, 15, 20, 25]
private abbrev setup : Table (ZMod babyBearModulus) (fields 8) := Keccak.setupTable control
private def reads (case : Fin 3) : Vector Nat 6 := Vector.ofFn fun i =>
  if h : i.val < 5 then referenceState[5 * (selectedColumn case).val + i.val] else 0
private def changed (case : Fin 3) : Nat := (reads case)[0] ^^^ Keccak.adjustedConstant (effectiveRound case)
private def temps (case : Fin 3) : Vector Nat 3 :=
  #v[changed case ^^^ (reads case)[1], changed case ^^^ (reads case)[1] ^^^ (reads case)[2],
    changed case ^^^ (reads case)[1] ^^^ (reads case)[2] ^^^ (reads case)[3]]
private def writes (case : Fin 3) : Vector Nat 6 :=
  #v[changed case, (reads case)[1], (reads case)[2], (reads case)[3], (reads case)[4],
    (temps case)[2] ^^^ (reads case)[4]]
private def aWords (case : Fin 3) : Vector Nat 5 :=
  #v[(reads case)[0], changed case, (temps case)[0], (temps case)[1], (temps case)[2]]
private def cWords (case : Fin 3) : Vector Nat 5 :=
  #v[changed case, (temps case)[0], (temps case)[1], (temps case)[2], (writes case)[5]]

private def row (case : Fin 3) (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 63 ∨ v = 70 + (selectedColumn case).val then 1
  else if v = 3 then (stateControl case).packed
  else if v = 5 then (stateControl case).nextPacked
  else if 7 ≤ v ∧ v < 13 then (5 * (v - 7) : Nat)
  else if h : 15 ≤ v ∧ v < 63 then
    let lane : Fin 6 := ⟨(v - 15) / 8, by omega⟩
    let limb := ((v - 15) % 8) / 4 * 2 + (v - 15) % 2
    let value := if (v - 15) % 4 < 2 then (reads case)[lane] else (writes case)[lane]
    (value / 2 ^ (16 * limb) % 65536 : Nat)
  else if 75 ≤ v ∧ v < 80 then ((selectedRound case).val / 2 ^ (v - 75) % 2 : Nat)
  else if v = 85 then effectiveRound case
  else if 86 ≤ v ∧ v < 90 then
    (effectiveRound case + 64 * (v - 86) + 256 * (effectiveRound case + 64 * (v - 86) + 32) : Nat)
  else if h : 90 ≤ v ∧ v < 102 then
    let temporary : Fin 3 := ⟨(v - 90) / 4, by omega⟩
    ((temps case)[temporary] / 2 ^ (16 * ((v - 90) % 4)) % 65536 : Nat)
  else if h : 102 ≤ v ∧ v < 222 then
    let operation : Fin 5 := ⟨(v - 102) / 24, by omega⟩
    let column := ((v - 102) % 24) / 8
    let byte := (v - 102) % 8
    if column = 1 ∧ operation.val = 0 then (effectiveRound case + 32 * byte : Nat)
    else
      let value := if column = 0 then (aWords case)[operation]
        else if column = 1 then (reads case)[operation] else (cWords case)[operation]
      (value / 2 ^ (8 * byte) % 256 : Nat)
  else 0

private def byteIndex (case : Fin 3) (i : Fin 40) : Nat :=
  let op : Fin 5 := ⟨i.val / 8, by omega⟩
  let a := (aWords case)[op] / 2 ^ (8 * (i.val % 8)) % 256
  let b := if op.val = 0 then effectiveRound case + 32 * (i.val % 8)
    else (reads case)[op] / 2 ^ (8 * (i.val % 8)) % 256
  if op.val = 0 then 69633 + a + 256 * b else 1 + 256 * a + b

private theorem byteIndexBound (case : Fin 3) (i : Fin 40) : byteIndex case i < 1249281 := by
  fin_cases case <;> fin_cases i <;> decide

private theorem byteValues (case : Fin 3) (i : Fin 40) :
    (Keccak.Proofs.byteEntry setup i).map (Expression.eval (Verification.environment (row case))) =
      (Keccak.setupRow control ⟨byteIndex case i, byteIndexBound case i⟩).map
        (fun (n : Nat) => (n : ZMod babyBearModulus)) := by
  simp only [Keccak.Proofs.setup_row_characterization]
  fin_cases case <;> fin_cases i <;>
    dsimp [Keccak.Proofs.byteEntry, Keccak.Proofs.byteQuery,
      Keccak.importedConstraints, FlatOperation.lookups]
  all_goals
    apply Vector.ext
    intro j hj
    change j < 8 at hj
    interval_cases j <;> simp only [Vector.getElem_map, Vector.getElem_cast] <;> decide +kernel +revert

private theorem bytesHold (case : Fin 3) (i : Fin 40) :
    (Keccak.Proofs.byteQuery setup i).Contains (Verification.environment (row case)) := by
  rw [Keccak.Proofs.byte_query_shape]
  exact ⟨⟨byteIndex case i, byteIndexBound case i⟩, byteValues case i⟩

private theorem controllerHolds (case : Fin 3) :
    ((FlatOperation.lookups (Keccak.importedConstraints setup)).get
      ⟨1, by rw [Keccak.lookup_count]; decide⟩).Contains (Verification.environment (row case)) := by
  change ∃ index : Fin 1249281,
    ((FlatOperation.lookups (Keccak.importedConstraints setup))[1]).entry.map
      (Expression.eval (Verification.environment (row case))) =
      (Keccak.setupRow control index).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨⟨65537 + 2048 + (stateControl case).packed, by fin_cases case <;> decide⟩, ?_⟩
  fin_cases case <;> dsimp [Keccak.importedConstraints, FlatOperation.lookups]
  all_goals
    apply Vector.ext
    intro j hj
    change j < 8 at hj
    interval_cases j <;> simp only [Vector.getElem_map] <;> decide +kernel +revert

theorem satisfies (case : Fin 3) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row case))
      (Keccak.importedConstraints setup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · fin_cases case <;> decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 42 := by simpa only [Keccak.lookup_count] using hi
    by_cases range : i = 0
    · subst i
      apply Trace.Proofs.range_contains
      fin_cases case <;> decide
    by_cases controller : i = 1
    · subst i
      simpa only [List.get_eq_getElem] using controllerHolds case
    have relation := bytesHold case ⟨i - 2, by omega⟩
    have index : i - 2 + 2 = i := by omega
    simpa only [Keccak.Proofs.byteQuery, List.get_eq_getElem, Fin.val_mk, index] using relation

theorem nativeMapping (case : Fin 3) :
    Keccak.IotaMapping referenceState (selectedColumn case) (selectedRound case) (row case) := by
  constructor
  · fin_cases case <;> decide
  · fin_cases case <;> decide
  · intro i; fin_cases case <;> fin_cases i <;> decide

theorem referenceColumn (case : Fin 3) :
    Keccak.IotaResult referenceState (selectedColumn case) (selectedRound case) (row case) :=
  Keccak.iota_column_soundness (by decide) (satisfies case) (nativeMapping case)

private theorem expected_nonzero :
    (Keccak.iotaState referenceState (24 : Fin 25))[0] ≠ 0 := by decide

theorem wrongWriteRejected {w : Nat → ZMod babyBearModulus}
    (mapping : Keccak.IotaMapping referenceState (0 : Fin 5) (24 : Fin 25) w)
    (wrong : Keccak.writeLane w 0 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Keccak.importedConstraints setup) := by
  intro holds
  have result := (Keccak.iota_column_soundness (by decide) holds mapping).1 (0 : Fin 5)
  change Keccak.writeLane w 0 = (Keccak.iotaState referenceState (24 : Fin 25))[0] at result
  rw [wrong] at result
  exact expected_nonzero result.symm

theorem caller_first_control : (row 0 5).val = (Keccak.scheduleControl 1).packed := by
  have result := Keccak.Proofs.forced_schedule_step (by decide : 4096 ≤ babyBearModulus)
    (0 : Fin 649) (satisfies 0) (by decide) (by decide)
  exact result

theorem caller_final_control : (row 1 5).val = 1544 := by
  have result := Keccak.Proofs.forced_schedule_step (by decide : 4096 ≤ babyBearModulus)
    (648 : Fin 649) (satisfies 1) (by decide) (by decide)
  change (row 1 5).val = (Keccak.scheduleControl 649).packed at result
  simpa only [Keccak.Proofs.schedule_finish] using result

end Tests.KeccakIota

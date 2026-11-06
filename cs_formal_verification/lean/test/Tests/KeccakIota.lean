import Slop.Keccak.Claims
import Slop.BabyBear
import Mathlib.Tactic.IntervalCases
import Slop.Keccak.Completeness.Bytes

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

private def base (case : Fin 3) (v : Nat) : ZMod babyBearModulus :=
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
  else 0

-- Byte query `i` (operation `i / 8`, byte `i % 8`): the Iota XOR of lane 0 with the round
-- constant, then the running XOR of the column.
private def bytes (case : Fin 3) (part : Fin 3) (i : Fin 40) : Nat :=
  let op : Fin 5 := ⟨i.val / 8, by omega⟩
  if op.val = 0 then
    if part.val = 0 then Keccak.Proofs.wordByte (reads case)[0] (i.val % 8)
    else if part.val = 1 then effectiveRound case + 32 * (i.val % 8)
    else Keccak.Proofs.wordByte ((reads case)[0] ^^^ Keccak.adjustedConstant (effectiveRound case)) (i.val % 8)
  else Keccak.Proofs.wordByte (if part.val = 0 then (aWords case)[op]
    else if part.val = 1 then (reads case)[op] else (aWords case)[op] ^^^ (reads case)[op]) (i.val % 8)

private def row (case : Fin 3) : Nat → ZMod babyBearModulus :=
  Keccak.Proofs.bytesRow (base case) (bytes case)

private theorem modes (case : Fin 3) (j : Fin 7) :
    row case Keccak.Variables.modeColumns[j] = if j = 0 then 1 else 0 := by
  fin_cases case <;> fin_cases j <;> decide

private theorem round_bound (case : Fin 3) : effectiveRound case < 32 := by
  fin_cases case <;> decide

private theorem bytesHold (case : Fin 3) (i : Fin 40) :
    (Keccak.Proofs.byteQuery setup i).Contains (Verification.environment (row case)) := by
  have tag := Keccak.Proofs.byte_tag_of_mode setup _ (modes case) i
  have byte (part : Fin 3) : row case (Keccak.Proofs.byteColumn part i) = (bytes case part i : Nat) :=
    Keccak.Proofs.bytes_row_byte _ _ part i
  by_cases first : i.val / 8 = 0
  · have op : (⟨i.val / 8, by omega⟩ : Fin 5) = 0 := Fin.ext first
    rw [op, show Keccak.Proofs.operationTag 0 0 = 38 from rfl] at tag
    refine Keccak.Proofs.iota_query i (reads case)[0] (round_bound case) ?_ ?_ ?_ tag
    all_goals rw [byte]; simp only [bytes, first, ↓reduceIte, Fin.isValue]; rfl
  · have op : (⟨i.val / 8, by omega⟩ : Fin 5) ≠ 0 := fun h => first (congrArg Fin.val h)
    have xor : ∀ op : Fin 5, op ≠ 0 → Keccak.Proofs.operationTag 0 op = 4 := by decide
    rw [xor _ op] at tag
    refine Keccak.Proofs.xor_query i (aWords case)[(⟨i.val / 8, by omega⟩ : Fin 5)]
      (reads case)[(⟨i.val / 8, by omega⟩ : Fin 5)] ?_ ?_ ?_ tag
    all_goals rw [byte]; simp only [bytes, first, ↓reduceIte, Fin.isValue]; rfl

private theorem controllerHolds (case : Fin 3) :
    ((FlatOperation.lookups (Keccak.importedConstraints setup)).get
      ⟨1, by rw [Keccak.lookup_count]; decide⟩).Contains (Verification.environment (row case)) := by
  refine Keccak.Proofs.controller_query (key := 2048 + (stateControl case).packed) (by fin_cases case <;> decide) ?_ ?_
  · fin_cases case <;> decide
  · fin_cases case <;> decide

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
      apply Verification.range16_contains
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

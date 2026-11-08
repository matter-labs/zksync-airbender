module
public import Slop.Keccak.PhaseDefinitions
public import Slop.Keccak.ReferenceLemmas

@[expose] public section

/-! Generic lemmas for the special5 calls, proven once for every round: a call writes its six slots
with its micro-operation values and leaves every other slot alone. The slots of every call are closed
data, checked once per call kind for all rounds against the Pi lane layout. -/

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- The physical slot of logical lane `lane` before round `round`. -/
def physicalCell (round : Nat) (lane : Fin 25) : Fin 31 :=
  ⟨Controller.physicalLane round lane,
    Nat.lt_trans (Controller.Proofs.physical_bound round lane) (by decide)⟩

theorem physical_cell_bound (round : Nat) (lane : Fin 25) : (physicalCell round lane).val < 25 :=
  Controller.Proofs.physical_bound round lane

theorem physical_cell_eq_iff (round : Nat) (a b : Fin 25) :
    physicalCell round a = physicalCell round b ↔ a = b :=
  ⟨fun same => Controller.Proofs.physical_injective round (congrArg Fin.val same),
    fun same => same ▸ rfl⟩

theorem logical_lanes_entry (round : Nat) (state : LaneState) (lane : Nat) (bound : lane < 25) :
    (logicalLanes round state)[lane] = state (physicalCell round ⟨lane, bound⟩) := by
  simp only [logicalLanes, Vector.getElem_ofFn]
  rfl

/-! ### One call -/

/-- The six lane values call `call` reads, in port order. -/
def callReads (call : Fin 649) (state : LaneState) (lane : Fin 6) : Nat :=
  state ⟨(slotIndices call)[lane], Controller.Proofs.rows_bound _ lane⟩

/-- The slot a call accesses through port `j`. -/
def callSlot (call : Fin 649) (j : Fin 6) : Fin 31 :=
  ⟨(slotIndices call)[j], Controller.Proofs.rows_bound _ j⟩

theorem call_reads_entry (call : Fin 649) (state : LaneState) (j : Fin 6) :
    callReads call state j = state (callSlot call j) := rfl

/-- A call writes the slot of port `j` with its `j`-th micro-operation value. -/
theorem micro_step_slot {call : Fin 649} (distinct : (slotIndices call).toList.Nodup) (state : LaneState)
    (j : Fin 6) :
    microStep call state (callSlot call j) =
      microValue (scheduleControl ⟨call.val, by omega⟩) (callReads call state) j := by
  have position : (slotIndices call).toList.idxOf (callSlot call j).val = j.val := by
    have := distinct.idxOf_getElem j.val (by simp only [Vector.length_toList]; omega)
    simpa only [Vector.getElem_toList, callSlot, Fin.getElem_fin] using this
  have active : (slotIndices call).toList.idxOf (callSlot call j).val < 6 := by
    rw [position]
    exact j.isLt
  show (if h : _ < 6 then _ else _) = _
  rw [dite_eq_left active]
  congr 1
  exact Fin.ext position

/-- A call leaves every slot it does not access unchanged. -/
theorem micro_step_frame (call : Fin 649) (state : LaneState) (physical : Fin 31)
    (other : ∀ j : Fin 6, callSlot call j ≠ physical) :
    microStep call state physical = state physical := by
  apply dite_eq_right
  intro active
  apply other ⟨_, active⟩
  apply Fin.ext
  have found := List.getElem_idxOf (xs := (slotIndices call).toList) (x := physical.val)
    (by simpa only [Vector.length_toList] using active)
  simpa only [Vector.getElem_toList, callSlot, Fin.getElem_fin] using found

/-- A call that writes back what it reads through port `j` leaves that slot unchanged too. -/
theorem micro_step_kept {call : Fin 649} (distinct : (slotIndices call).toList.Nodup) (state : LaneState)
    (physical : Fin 31)
    (other : ∀ j : Fin 6, callSlot call j = physical →
      microValue (scheduleControl ⟨call.val, by omega⟩) (callReads call state) j = state physical) :
    microStep call state physical = state physical := by
  by_cases hit : ∃ j : Fin 6, callSlot call j = physical
  · obtain ⟨j, same⟩ := hit
    subst same
    rw [micro_step_slot distinct]
    exact other j rfl
  · exact micro_step_frame call state physical fun j same => hit ⟨j, same⟩

/-! ### The schedule's controls -/

theorem schedule_control_at {call : Fin 649} {round stage : Nat} (shape : call.val = 27 * round + stage)
    (small : stage < 27) {mode : Fin 7} {iteration : Fin 5}
    (modeEq : mode.val = if stage < 5 then 0 else if stage < 7 then stage - 4 else if stage < 12 then 3
      else if stage < 17 then 4 else if (stage - 17) % 2 = 0 then 5 else 6)
    (iterationEq : iteration.val = if stage < 5 then stage else if stage < 7 then 0
      else if stage < 12 then stage - 7 else if stage < 17 then stage - 12 else (stage - 17) / 2) :
    scheduleControl ⟨call.val, by omega⟩ = ⟨mode, iteration, ⟨round, by omega⟩⟩ := by
  have stageEq : call.val % 27 = stage := by omega
  have roundEq : call.val / 27 = round := by omega
  simp only [scheduleControl, ControlState.mk.injEq, Fin.ext_iff, stageEq, roundEq, modeEq, iterationEq,
    and_self]

/-! ### Closed slot tables, one per call kind, quantified over the round

`Vector.ofFn` unfolds by well-founded recursion, slow in the kernel: the controller rows are first
rewritten to six-entry literals. -/

private theorem of_fn_six {α : Type} (f : Fin 6 → α) : Vector.ofFn f = #v[f 0, f 1, f 2, f 3, f 4, f 5] := by
  ext i bound
  simp only [Vector.getElem_ofFn]
  interval_cases i <;> rfl

private theorem iota_table : ∀ round : Fin 25, ∀ column : Fin 5,
    ∀ valid : 27 * round.val + column.val < 649,
      (∀ j : Fin 5, (slotIndices ⟨27 * round.val + column.val, valid⟩)[j.val] =
        Controller.physicalLane round ⟨5 * column.val + j.val, by omega⟩) ∧
      (slotIndices ⟨27 * round.val + column.val, valid⟩)[5] = 25 + column.val ∧
      (slotIndices ⟨27 * round.val + column.val, valid⟩).toList.Nodup := by
  simp only [slotIndices, Controller.rows, of_fn_six]
  decide +kernel

private theorem theta_table : ∀ round : Fin 24, ∀ column : Fin 5,
    (∀ j : Fin 5, (slotIndices ⟨27 * round.val + 7 + column.val, by omega⟩)[j.val] =
      Controller.physicalLane round ⟨5 * column.val + j.val, by omega⟩) ∧
    (slotIndices ⟨27 * round.val + 7 + column.val, by omega⟩)[5] = 25 + (column.val + 4) % 5 ∧
    (slotIndices ⟨27 * round.val + 7 + column.val, by omega⟩).toList.Nodup := by
  simp only [slotIndices, Controller.rows, of_fn_six]
  decide +kernel

private theorem rho_table : ∀ round : Fin 24, ∀ column : Fin 5,
    (∀ j : Fin 5, (slotIndices ⟨27 * round.val + 12 + column.val, by omega⟩)[j.val] =
      Controller.physicalLane round ⟨5 * column.val + j.val, by omega⟩) ∧
    (slotIndices ⟨27 * round.val + 12 + column.val, by omega⟩)[5] = 25 ∧
    (slotIndices ⟨27 * round.val + 12 + column.val, by omega⟩).toList.Nodup := by
  simp only [slotIndices, Controller.rows, of_fn_six]
  decide +kernel

private theorem chi_first_table : ∀ round : Fin 24, ∀ row : Fin 5,
    (slotIndices ⟨27 * round.val + 17 + 2 * row.val, by omega⟩)[0] =
      Controller.physicalLane (round.val + 1) ⟨row.val + 5, by omega⟩ ∧
    (slotIndices ⟨27 * round.val + 17 + 2 * row.val, by omega⟩)[1] =
      Controller.physicalLane (round.val + 1) ⟨row.val + 10, by omega⟩ ∧
    (slotIndices ⟨27 * round.val + 17 + 2 * row.val, by omega⟩)[2] =
      Controller.physicalLane (round.val + 1) ⟨row.val + 15, by omega⟩ ∧
    (slotIndices ⟨27 * round.val + 17 + 2 * row.val, by omega⟩)[3] =
      Controller.physicalLane (round.val + 1) ⟨row.val + 20, by omega⟩ ∧
    (slotIndices ⟨27 * round.val + 17 + 2 * row.val, by omega⟩)[4] = 25 ∧
    (slotIndices ⟨27 * round.val + 17 + 2 * row.val, by omega⟩)[5] = 26 ∧
    (slotIndices ⟨27 * round.val + 17 + 2 * row.val, by omega⟩).toList.Nodup := by
  simp only [slotIndices, Controller.rows, of_fn_six]
  decide +kernel

private theorem chi_second_table : ∀ round : Fin 24, ∀ row : Fin 5,
    (slotIndices ⟨27 * round.val + 18 + 2 * row.val, by omega⟩)[0] =
      Controller.physicalLane (round.val + 1) ⟨row.val, by omega⟩ ∧
    (slotIndices ⟨27 * round.val + 18 + 2 * row.val, by omega⟩)[1] =
      Controller.physicalLane (round.val + 1) ⟨row.val + 15, by omega⟩ ∧
    (slotIndices ⟨27 * round.val + 18 + 2 * row.val, by omega⟩)[2] =
      Controller.physicalLane (round.val + 1) ⟨row.val + 20, by omega⟩ ∧
    (slotIndices ⟨27 * round.val + 18 + 2 * row.val, by omega⟩)[3] = 25 ∧
    (slotIndices ⟨27 * round.val + 18 + 2 * row.val, by omega⟩)[4] = 26 ∧
    (slotIndices ⟨27 * round.val + 18 + 2 * row.val, by omega⟩)[5] = 27 ∧
    (slotIndices ⟨27 * round.val + 18 + 2 * row.val, by omega⟩).toList.Nodup := by
  simp only [slotIndices, Controller.rows, of_fn_six]
  decide +kernel

/-! ### Iota calls (mode 0): column `column` of round `round` -/

section Iota
variable {call : Fin 649} {round column : Nat} (shape : call.val = 27 * round + column) (small : column < 5)
include shape small

theorem iota_slot_lane (j : Nat) (position : j < 5) :
    callSlot call ⟨j, by omega⟩ = physicalCell round ⟨5 * column + j, by omega⟩ := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  exact Fin.ext ((iota_table ⟨round, by omega⟩ ⟨column, small⟩ bound).1 ⟨j, position⟩)

theorem iota_slot_five : callSlot call 5 = ⟨25 + column, by omega⟩ := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  exact Fin.ext (iota_table ⟨round, by omega⟩ ⟨column, small⟩ bound).2.1

theorem iota_nodup : (slotIndices call).toList.Nodup := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  exact (iota_table ⟨round, by omega⟩ ⟨column, small⟩ bound).2.2

theorem iota_control :
    scheduleControl ⟨call.val, by omega⟩ = ⟨0, ⟨column, small⟩, ⟨round, by omega⟩⟩ :=
  schedule_control_at shape (by omega) (by simp only [small, ↓reduceIte, Fin.val_zero])
    (by simp only [small, ↓reduceIte])

/-- Iota call `column` writes lane `j` of its column: unchanged, except the delayed round constant on
    lane (0, 0) after round zero. -/
theorem iota_step_lane (state : LaneState) {lane : Fin 25} {j : Nat} (position : j < 5)
    (hlane : lane.val = 5 * column + j) :
    microStep call state (physicalCell round lane) =
      if lane.val = 0 ∧ 0 < round then
        state (physicalCell round lane) ^^^ (roundConstants[Fin.ofNat 24 (round - 1)].toFin : Nat)
      else state (physicalCell round lane) := by
  obtain ⟨lane, bound⟩ := lane
  simp only at hlane
  subst hlane
  rw [← iota_slot_lane shape small j position, micro_step_slot (iota_nodup shape small),
    iota_control shape small]
  simp only [microValue, iotaValue, dite_eq_ite, ↓reduceIte, call_reads_entry, position, Fin.isValue]
  have same : (column = 0 ∧ j = 0 ∧ 0 < round) ↔ (5 * column + j = 0 ∧ 0 < round) := by omega
  simp only [same]

/-- Iota call `column` writes C[column] of its column after the delayed round constant. -/
theorem iota_step_parity (state : LaneState) :
    microStep call state ⟨25 + column, by omega⟩ =
      (if column = 0 ∧ 0 < round then
        state (physicalCell round ⟨5 * column, by omega⟩) ^^^
          (roundConstants[Fin.ofNat 24 (round - 1)].toFin : Nat)
      else state (physicalCell round ⟨5 * column, by omega⟩)) ^^^
        state (physicalCell round ⟨5 * column + 1, by omega⟩) ^^^
        state (physicalCell round ⟨5 * column + 2, by omega⟩) ^^^
        state (physicalCell round ⟨5 * column + 3, by omega⟩) ^^^
        state (physicalCell round ⟨5 * column + 4, by omega⟩) := by
  have l0 : callSlot call 0 = physicalCell round ⟨5 * column, by omega⟩ := iota_slot_lane shape small 0 (by decide)
  have l1 : callSlot call 1 = physicalCell round ⟨5 * column + 1, by omega⟩ :=
    iota_slot_lane shape small 1 (by decide)
  have l2 : callSlot call 2 = physicalCell round ⟨5 * column + 2, by omega⟩ :=
    iota_slot_lane shape small 2 (by decide)
  have l3 : callSlot call 3 = physicalCell round ⟨5 * column + 3, by omega⟩ :=
    iota_slot_lane shape small 3 (by decide)
  have l4 : callSlot call 4 = physicalCell round ⟨5 * column + 4, by omega⟩ :=
    iota_slot_lane shape small 4 (by decide)
  rw [← iota_slot_five shape small, micro_step_slot (iota_nodup shape small), iota_control shape small]
  simp only [microValue, iotaValue, dite_eq_ite, ↓reduceIte, call_reads_entry, Fin.isValue, l0, l1, l2, l3, l4,
    show ¬ (5 : Fin 6).val < 5 by decide, show (0 : Fin 6).val = 0 from rfl, true_and]

/-- An iota call leaves every slot but its column and C[column] unchanged. -/
theorem iota_step_kept (state : LaneState) (physical : Fin 31)
    (lanes : ∀ j (position : j < 5), physicalCell round ⟨5 * column + j, by omega⟩ ≠ physical)
    (parity : (⟨25 + column, by omega⟩ : Fin 31) ≠ physical) :
    microStep call state physical = state physical := by
  apply micro_step_frame
  intro ⟨j, bound⟩
  by_cases lane : j < 5
  · rw [iota_slot_lane shape small j lane]
    exact lanes j lane
  · obtain rfl : j = 5 := by omega
    exact fun same => parity ((iota_slot_five shape small).symm.trans same)

end Iota

/-! ### Theta calls (mode 3): column `column` of round `round` -/

section Theta
variable {call : Fin 649} {round column : Nat} (shape : call.val = 27 * round + 7 + column)
  (small : column < 5)
include shape small

theorem theta_slot_lane (j : Nat) (position : j < 5) :
    callSlot call ⟨j, by omega⟩ = physicalCell round ⟨5 * column + j, by omega⟩ := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  exact Fin.ext ((theta_table ⟨round, by omega⟩ ⟨column, small⟩).1 ⟨j, position⟩)

theorem theta_slot_five : callSlot call 5 = ⟨25 + (column + 4) % 5, by omega⟩ := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  exact Fin.ext (theta_table ⟨round, by omega⟩ ⟨column, small⟩).2.1

theorem theta_nodup : (slotIndices call).toList.Nodup := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  exact (theta_table ⟨round, by omega⟩ ⟨column, small⟩).2.2

theorem theta_control :
    scheduleControl ⟨call.val, by omega⟩ = ⟨3, ⟨column, small⟩, ⟨round, by omega⟩⟩ :=
  schedule_control_at (stage := 7 + column) (by omega) (by omega)
    (by simp only [show ¬ 7 + column < 5 by omega, show ¬ 7 + column < 7 by omega,
      show 7 + column < 12 by omega, ↓reduceIte]; rfl)
    (by simp only [show ¬ 7 + column < 5 by omega, show ¬ 7 + column < 7 by omega,
      show 7 + column < 12 by omega, ↓reduceIte]; omega)

/-- Theta call `column` xors D[column] into lane `j` of its column. -/
theorem theta_step_lane (state : LaneState) {lane : Fin 25} {j : Nat} (position : j < 5)
    (hlane : lane.val = 5 * column + j) :
    microStep call state (physicalCell round lane) =
      state (physicalCell round lane) ^^^ state ⟨25 + (column + 4) % 5, by omega⟩ := by
  obtain ⟨lane, bound⟩ := lane
  simp only at hlane
  subst hlane
  rw [← theta_slot_lane shape small j position, micro_step_slot (theta_nodup shape small),
    theta_control shape small]
  simp only [microValue, Fin.isValue, Fin.reduceEq, ↓reduceIte, position, call_reads_entry,
    theta_slot_five shape small]

/-- A theta call leaves every slot but its column unchanged (it writes D back as read). -/
theorem theta_step_kept (state : LaneState) (physical : Fin 31)
    (lanes : ∀ j (position : j < 5), physicalCell round ⟨5 * column + j, by omega⟩ ≠ physical) :
    microStep call state physical = state physical := by
  apply micro_step_kept (theta_nodup shape small)
  intro ⟨j, bound⟩ same
  by_cases lane : j < 5
  · rw [theta_slot_lane shape small j lane] at same
    exact absurd same (lanes j lane)
  · obtain rfl : j = 5 := by omega
    subst same
    rw [theta_control shape small]
    simp only [microValue, Fin.isValue, Fin.reduceEq, ↓reduceIte, call_reads_entry]
    rfl

end Theta

/-! ### Rho calls (mode 4): column `column` of round `round` -/

section Rho
variable {call : Fin 649} {round column : Nat} (shape : call.val = 27 * round + 12 + column)
  (small : column < 5)
include shape small

theorem rho_slot_lane (j : Nat) (position : j < 5) :
    callSlot call ⟨j, by omega⟩ = physicalCell round ⟨5 * column + j, by omega⟩ := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  exact Fin.ext ((rho_table ⟨round, by omega⟩ ⟨column, small⟩).1 ⟨j, position⟩)

theorem rho_nodup : (slotIndices call).toList.Nodup := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  exact (rho_table ⟨round, by omega⟩ ⟨column, small⟩).2.2

theorem rho_control :
    scheduleControl ⟨call.val, by omega⟩ = ⟨4, ⟨column, small⟩, ⟨round, by omega⟩⟩ :=
  schedule_control_at (stage := 12 + column) (by omega) (by omega)
    (by simp only [show ¬ 12 + column < 5 by omega, show ¬ 12 + column < 7 by omega,
      show ¬ 12 + column < 12 by omega, show 12 + column < 17 by omega, ↓reduceIte]; rfl)
    (by simp only [show ¬ 12 + column < 5 by omega, show ¬ 12 + column < 7 by omega,
      show ¬ 12 + column < 12 by omega, show 12 + column < 17 by omega, ↓reduceIte]; omega)

/-- Rho call `column` rotates lane `j` of its column by its offset. -/
theorem rho_step_lane (state : LaneState) {lane : Fin 25} {j : Nat} (position : j < 5)
    (hlane : lane.val = 5 * column + j) :
    microStep call state (physicalCell round lane) =
      rotLeft64 (state (physicalCell round lane)) ((rhoRotations[column]'small)[j]'position) := by
  obtain ⟨lane, bound⟩ := lane
  simp only at hlane
  subst hlane
  rw [← rho_slot_lane shape small j position, micro_step_slot (rho_nodup shape small),
    rho_control shape small]
  simp only [microValue, Fin.isValue, Fin.reduceEq, ↓reduceIte, position, dite_true, call_reads_entry,
    Fin.getElem_fin]

/-- A rho call leaves every slot but its column unchanged (it writes its scratch read back). -/
theorem rho_step_kept (state : LaneState) (physical : Fin 31)
    (lanes : ∀ j (position : j < 5), physicalCell round ⟨5 * column + j, by omega⟩ ≠ physical) :
    microStep call state physical = state physical := by
  apply micro_step_kept (rho_nodup shape small)
  intro ⟨j, bound⟩ same
  by_cases lane : j < 5
  · rw [rho_slot_lane shape small j lane] at same
    exact absurd same (lanes j lane)
  · obtain rfl : j = 5 := by omega
    subst same
    rw [rho_control shape small]
    simp only [microValue, Fin.isValue, Fin.reduceEq, ↓reduceIte, call_reads_entry]
    rfl

end Rho

/-! ### Chi calls (modes 5 and 6): row `row` of round `round`, lanes after the Pi renaming -/

/-- The physical slot of lane (x, row) before round `round + 1`. -/
def chiCell (round : Nat) (row x : Fin 5) : Fin 31 :=
  physicalCell (round + 1) ⟨row.val + 5 * x.val, by omega⟩

theorem chi_cell_bound (round : Nat) (row x : Fin 5) : (chiCell round row x).val < 25 :=
  physical_cell_bound _ _

theorem chi_cell_ne {round : Nat} {row row' x x' : Fin 5} (different : row ≠ row' ∨ x ≠ x') :
    chiCell round row x ≠ chiCell round row' x' := by
  intro same
  rw [chiCell, chiCell, physical_cell_eq_iff, Fin.mk.injEq] at same
  rcases different with different | different
  · exact different (Fin.ext (by omega))
  · exact different (Fin.ext (by omega))

section ChiFirst
variable {call : Fin 649} {round : Nat} {row : Fin 5} (shape : call.val = 27 * round + 17 + 2 * row.val)
include shape

theorem chi_first_slots :
    callSlot call 0 = chiCell round row 1 ∧ callSlot call 1 = chiCell round row 2 ∧
    callSlot call 2 = chiCell round row 3 ∧ callSlot call 3 = chiCell round row 4 ∧
    callSlot call 4 = ⟨25, by decide⟩ ∧ callSlot call 5 = ⟨26, by decide⟩ := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  obtain ⟨zero, one, two, three, four, five, -⟩ := chi_first_table ⟨round, by omega⟩ row
  exact ⟨Fin.ext zero, Fin.ext one, Fin.ext two, Fin.ext three, Fin.ext four, Fin.ext five⟩

theorem chi_first_nodup : (slotIndices call).toList.Nodup := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  exact (chi_first_table ⟨round, by omega⟩ row).2.2.2.2.2.2

theorem chi_first_control :
    scheduleControl ⟨call.val, by omega⟩ = ⟨5, row, ⟨round, by omega⟩⟩ :=
  schedule_control_at (stage := 17 + 2 * row.val) (by omega) (by omega)
    (by simp only [show ¬ 17 + 2 * row.val < 5 by omega, show ¬ 17 + 2 * row.val < 7 by omega,
      show ¬ 17 + 2 * row.val < 12 by omega, show ¬ 17 + 2 * row.val < 17 by omega,
      show (17 + 2 * row.val - 17) % 2 = 0 by omega, ↓reduceIte]; rfl)
    (by simp only [show ¬ 17 + 2 * row.val < 5 by omega, show ¬ 17 + 2 * row.val < 7 by omega,
      show ¬ 17 + 2 * row.val < 12 by omega, show ¬ 17 + 2 * row.val < 17 by omega, ↓reduceIte]; omega)

/-- The first chi call of a row: lanes x = 1, 2 get their chi value, lanes x = 3, 4 are written back,
    scratch 25 gets (not b1) and b2, scratch 26 gets b1. -/
theorem chi_first_values (state : LaneState) :
    microStep call state (chiCell round row 1) = state (chiCell round row 1) ^^^
      (not64 (state (chiCell round row 2)) &&& state (chiCell round row 3)) ∧
    microStep call state (chiCell round row 2) = state (chiCell round row 2) ^^^
      (not64 (state (chiCell round row 3)) &&& state (chiCell round row 4)) ∧
    microStep call state (chiCell round row 3) = state (chiCell round row 3) ∧
    microStep call state (chiCell round row 4) = state (chiCell round row 4) ∧
    microStep call state ⟨25, by decide⟩ =
      not64 (state (chiCell round row 1)) &&& state (chiCell round row 2) ∧
    microStep call state ⟨26, by decide⟩ = state (chiCell round row 1) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := chi_first_slots shape
  have value (j : Fin 6) : microStep call state (callSlot call j) =
      microValue ⟨5, row, ⟨round, by omega⟩⟩ (callReads call state) j := by
    rw [micro_step_slot (chi_first_nodup shape), chi_first_control shape]
  have v0 := value 0
  have v1 := value 1
  have v2 := value 2
  have v3 := value 3
  have v4 := value 4
  have v5 := value 5
  simp only [microValue, Fin.isValue, Fin.reduceEq, ↓reduceIte, call_reads_entry, s0, s1, s2, s3, s4,
    s5] at v0 v1 v2 v3 v4 v5
  exact ⟨v0, v1, v2, v3, v4, v5⟩

/-- The first chi call of a row leaves every slot but the row's lanes x = 1..4 and scratch 25, 26. -/
theorem chi_first_kept (state : LaneState) (physical : Fin 31)
    (lanes : ∀ x : Fin 5, x ≠ 0 → chiCell round row x ≠ physical)
    (scratch : physical.val ≠ 25 ∧ physical.val ≠ 26) :
    microStep call state physical = state physical := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := chi_first_slots shape
  apply micro_step_frame
  intro j
  fin_cases j
  · exact fun same => lanes 1 (by decide) (s0.symm.trans same)
  · exact fun same => lanes 2 (by decide) (s1.symm.trans same)
  · exact fun same => lanes 3 (by decide) (s2.symm.trans same)
  · exact fun same => lanes 4 (by decide) (s3.symm.trans same)
  · exact fun same => scratch.1 (congrArg Fin.val (s4.symm.trans same)).symm
  · exact fun same => scratch.2 (congrArg Fin.val (s5.symm.trans same)).symm

end ChiFirst

section ChiSecond
variable {call : Fin 649} {round : Nat} {row : Fin 5} (shape : call.val = 27 * round + 18 + 2 * row.val)
include shape

theorem chi_second_slots :
    callSlot call 0 = chiCell round row 0 ∧ callSlot call 1 = chiCell round row 3 ∧
    callSlot call 2 = chiCell round row 4 ∧ callSlot call 3 = ⟨25, by decide⟩ ∧
    callSlot call 4 = ⟨26, by decide⟩ ∧ callSlot call 5 = ⟨27, by decide⟩ := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  obtain ⟨zero, one, two, three, four, five, -⟩ := chi_second_table ⟨round, by omega⟩ row
  exact ⟨Fin.ext zero, Fin.ext one, Fin.ext two, Fin.ext three, Fin.ext four, Fin.ext five⟩

theorem chi_second_nodup : (slotIndices call).toList.Nodup := by
  obtain ⟨call, bound⟩ := call
  simp only at shape
  subst shape
  exact (chi_second_table ⟨round, by omega⟩ row).2.2.2.2.2.2

theorem chi_second_control :
    scheduleControl ⟨call.val, by omega⟩ = ⟨6, row, ⟨round, by omega⟩⟩ :=
  schedule_control_at (stage := 18 + 2 * row.val) (by omega) (by omega)
    (by simp only [show ¬ 18 + 2 * row.val < 5 by omega, show ¬ 18 + 2 * row.val < 7 by omega,
      show ¬ 18 + 2 * row.val < 12 by omega, show ¬ 18 + 2 * row.val < 17 by omega,
      show ¬ (18 + 2 * row.val - 17) % 2 = 0 by omega, ↓reduceIte]; rfl)
    (by simp only [show ¬ 18 + 2 * row.val < 5 by omega, show ¬ 18 + 2 * row.val < 7 by omega,
      show ¬ 18 + 2 * row.val < 12 by omega, show ¬ 18 + 2 * row.val < 17 by omega, ↓reduceIte]; omega)

/-- The second chi call of a row: lane x = 0 gets b0 ^ scratch 25, lane x = 3 gets
    b3 ^ (not b4 and b0), lane x = 4 gets b4 ^ (not b0 and scratch 26). -/
theorem chi_second_values (state : LaneState) :
    microStep call state (chiCell round row 0) =
      state (chiCell round row 0) ^^^ state ⟨25, by decide⟩ ∧
    microStep call state (chiCell round row 3) = state (chiCell round row 3) ^^^
      (not64 (state (chiCell round row 4)) &&& state (chiCell round row 0)) ∧
    microStep call state (chiCell round row 4) = state (chiCell round row 4) ^^^
      (not64 (state (chiCell round row 0)) &&& state ⟨26, by decide⟩) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := chi_second_slots shape
  have value (j : Fin 6) : microStep call state (callSlot call j) =
      microValue ⟨6, row, ⟨round, by omega⟩⟩ (callReads call state) j := by
    rw [micro_step_slot (chi_second_nodup shape), chi_second_control shape]
  have v0 := value 0
  have v1 := value 1
  have v2 := value 2
  simp only [microValue, Fin.isValue, Fin.reduceEq, ↓reduceIte, call_reads_entry, s0, s1, s2, s3,
    s4] at v0 v1 v2
  exact ⟨v0, v1, v2⟩

/-- The second chi call of a row leaves every slot but the row's lanes x = 0, 3, 4 unchanged (it writes
    scratch 25..27 back as read). -/
theorem chi_second_kept (state : LaneState) (physical : Fin 31)
    (lanes : ∀ x : Fin 5, (x = 0 ∨ x = 3 ∨ x = 4) → chiCell round row x ≠ physical) :
    microStep call state physical = state physical := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := chi_second_slots shape
  have value (j : Fin 6) : microStep call state (callSlot call j) =
      microValue ⟨6, row, ⟨round, by omega⟩⟩ (callReads call state) j := by
    rw [micro_step_slot (chi_second_nodup shape), chi_second_control shape]
  have v3 := value 3
  have v4 := value 4
  have v5 := value 5
  simp only [microValue, Fin.isValue, Fin.reduceEq, ↓reduceIte, call_reads_entry] at v3 v4 v5
  by_cases h3 : callSlot call 3 = physical
  · rw [← h3]
    exact v3
  by_cases h4 : callSlot call 4 = physical
  · rw [← h4]
    exact v4
  by_cases h5 : callSlot call 5 = physical
  · rw [← h5]
    exact v5
  apply micro_step_frame
  intro j
  fin_cases j
  · exact fun same => lanes 0 (by decide) (s0.symm.trans same)
  · exact fun same => lanes 3 (by decide) (s1.symm.trans same)
  · exact fun same => lanes 4 (by decide) (s2.symm.trans same)
  · exact h3
  · exact h4
  · exact h5

end ChiSecond

end Airbender.Keccak.Proofs

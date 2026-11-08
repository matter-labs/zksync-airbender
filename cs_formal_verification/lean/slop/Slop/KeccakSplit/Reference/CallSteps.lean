module
public import Slop.KeccakSplit.Reference.PermutationDefinitions
public import Slop.Keccak.ReferenceLemmas
import all Init.Data.Array.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

/-! Generic lemmas for the split reference calls, proven once for every round: a call writes its
accessed slots with its results and leaves every other slot alone, and a phase of five calls gives a
slot the value its owning call computes when no other call writes it or what the owner reads. The
slots of every call are closed data, checked once per phase kind against the Pi lane layout. -/

namespace Airbender.Keccak.Split.Call.Proofs
set_option warningAsError true

/-- The seven lane values call `index` reads, in port order. -/
def callInput (index : Fin 361) (state : LaneState) : Vector Nat 7 :=
  Vector.ofFn fun lane : Fin 7 => state (slots index)[lane]

/-- The physical slot of logical lane `lane` before round `round`. -/
def laneSlot (round : Nat) (lane : Fin 25) : Fin 31 :=
  ⟨Controller.physicalLane round lane,
    Nat.lt_trans (Controller.Proofs.physical_bound round lane) (by decide)⟩

theorem lane_slot_bound (round : Nat) (lane : Fin 25) : (laneSlot round lane).val < 25 :=
  Controller.Proofs.physical_bound round lane

theorem lane_slot_eq_iff (round : Nat) (a b : Fin 25) : laneSlot round a = laneSlot round b ↔ a = b :=
  ⟨fun same => Controller.Proofs.physical_injective round (congrArg Fin.val same),
    fun same => same ▸ rfl⟩

theorem logical_lanes_entry (round : Nat) (state : LaneState) (lane : Nat) (bound : lane < 25) :
    (logicalLanes round state)[lane] = state (laneSlot round ⟨lane, bound⟩) := by
  simp only [logicalLanes, Vector.getElem_ofFn]
  rfl

theorem micro_step_at {index : Fin 361} (state : LaneState) {physical : Fin 31} {j : Nat}
    (active : j < slotCount (kindAt index.val))
    (position : (slots index).toList.idxOf physical = j) :
    microStep index state physical =
      (result index (callInput index state))[j]'(lt_of_lt_of_le active (slot_count_bound _)) := by
  subst position
  exact dite_eq_left active

/-- A call writes its `j`-th accessed slot with its `j`-th result. -/
theorem micro_step_slot (index : Fin 361) (state : LaneState) {j : Nat}
    (active : j < slotCount (kindAt index.val)) :
    microStep index state ((slots index)[j]'(lt_of_lt_of_le active (slot_count_bound _))) =
      (result index (callInput index state))[j]'(lt_of_lt_of_le active (slot_count_bound _)) := by
  apply micro_step_at state active
  have length : j < ((slots index).toList.take (slotCount (kindAt index.val))).length := by
    simp only [List.length_take, Vector.length_toList]
    have := slot_count_bound (kindAt index.val)
    omega
  have first := (distinct_slots index).idxOf_getElem j length
  have member := List.getElem_mem length
  simp only [List.getElem_take, Vector.getElem_toList] at first member
  rw [← List.take_append_drop (slotCount (kindAt index.val)) (slots index).toList,
    List.idxOf_append_of_mem member]
  exact first

/-- A call leaves every slot it does not write unchanged. -/
theorem micro_step_frame (index : Fin 361) (state : LaneState) (physical : Fin 31)
    (other : ∀ j (active : j < slotCount (kindAt index.val)),
      (slots index)[j]'(lt_of_lt_of_le active (slot_count_bound _)) ≠ physical) :
    microStep index state physical = state physical := by
  apply dite_eq_right
  intro active
  apply other _ active
  have found := List.getElem_idxOf (xs := (slots index).toList) (x := physical)
    (by simp only [Vector.length_toList]; have := slot_count_bound (kindAt index.val); omega)
  simpa only [Vector.getElem_toList] using found

/-- A call's value at a slot depends only on the slots it reads and on that slot. -/
theorem micro_step_congr (index : Fin 361) {one two : LaneState} (physical : Fin 31)
    (reads : ∀ j : Fin 7, one (slots index)[j] = two (slots index)[j])
    (here : one physical = two physical) :
    microStep index one physical = microStep index two physical := by
  have inputs : callInput index one = callInput index two := by
    apply Vector.ext
    intro j bound
    simpa only [callInput, Vector.getElem_ofFn] using reads ⟨j, bound⟩
  show (if active : _ < _ then (result index (callInput index one))[_]'_ else one physical) =
    (if active : _ < _ then (result index (callInput index two))[_]'_ else two physical)
  rw [inputs, here]

/-! ### Closed slot data: one table per call kind, quantified over the round. -/

private theorem parity_table : ∀ round : Fin 25, ∀ column : Fin 5,
    ∀ valid : 15 * round.val + column.val < 361,
      (∀ j : Fin 5, ((slots ⟨15 * round.val + column.val, valid⟩)[j.val]'(by omega)).val =
        Controller.physicalLane round ⟨5 * column.val + j.val, by omega⟩) ∧
      ((slots ⟨15 * round.val + column.val, valid⟩)[5]).val = 25 + column.val ∧
      ((slots ⟨15 * round.val + column.val, valid⟩)[6]).val = 30 := by
  decide +kernel

private theorem theta_rho_table : ∀ round : Fin 24, ∀ column : Fin 5,
    (∀ j : Fin 5, ((slots ⟨15 * round.val + 5 + column.val, by omega⟩)[j.val]'(by omega)).val =
      Controller.physicalLane round ⟨5 * column.val + j.val, by omega⟩) ∧
    ((slots ⟨15 * round.val + 5 + column.val, by omega⟩)[5]).val = 25 + (column.val + 4) % 5 ∧
    ((slots ⟨15 * round.val + 5 + column.val, by omega⟩)[6]).val = 25 + (column.val + 1) % 5 := by
  decide +kernel

private theorem chi_table : ∀ round : Fin 24, ∀ row : Fin 5,
    (∀ j : Fin 5, ((slots ⟨15 * round.val + 10 + row.val, by omega⟩)[j.val]'(by omega)).val =
      Controller.physicalLane (round.val + 1)
        ⟨5 * ((j.val + 2 * row.val) % 5) + row.val, by omega⟩) ∧
    ((slots ⟨15 * round.val + 10 + row.val, by omega⟩)[5]).val = 30 ∧
    ((slots ⟨15 * round.val + 10 + row.val, by omega⟩)[6]).val = 30 := by
  decide +kernel

theorem parity_slot_lane {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + column) (valid : round < 25) (small : column < 5)
    (j : Nat) (position : j < 5) :
    (slots index)[j] = laneSlot round ⟨5 * column + j, by omega⟩ := by
  obtain ⟨index, bound⟩ := index
  simp only at shape
  subst shape
  exact Fin.ext ((parity_table ⟨round, valid⟩ ⟨column, small⟩ bound).1 ⟨j, position⟩)

theorem parity_slot_five {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + column) (valid : round < 25) (small : column < 5) :
    (slots index)[5] = ⟨25 + column, by omega⟩ := by
  obtain ⟨index, bound⟩ := index
  simp only at shape
  subst shape
  exact Fin.ext (parity_table ⟨round, valid⟩ ⟨column, small⟩ bound).2.1

theorem parity_slot_six {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + column) (valid : round < 25) (small : column < 5) :
    (slots index)[6] = 30 := by
  obtain ⟨index, bound⟩ := index
  simp only at shape
  subst shape
  exact Fin.ext (parity_table ⟨round, valid⟩ ⟨column, small⟩ bound).2.2

theorem theta_rho_slot_lane {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + 5 + column) (valid : round < 24) (small : column < 5)
    (j : Nat) (position : j < 5) :
    (slots index)[j] = laneSlot round ⟨5 * column + j, by omega⟩ := by
  obtain ⟨index, bound⟩ := index
  simp only at shape
  subst shape
  exact Fin.ext ((theta_rho_table ⟨round, valid⟩ ⟨column, small⟩).1 ⟨j, position⟩)

theorem theta_rho_slot_five {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + 5 + column) (valid : round < 24) (small : column < 5) :
    (slots index)[5] = ⟨25 + (column + 4) % 5, by omega⟩ := by
  obtain ⟨index, bound⟩ := index
  simp only at shape
  subst shape
  exact Fin.ext (theta_rho_table ⟨round, valid⟩ ⟨column, small⟩).2.1

theorem theta_rho_slot_six {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + 5 + column) (valid : round < 24) (small : column < 5) :
    (slots index)[6] = ⟨25 + (column + 1) % 5, by omega⟩ := by
  obtain ⟨index, bound⟩ := index
  simp only at shape
  subst shape
  exact Fin.ext (theta_rho_table ⟨round, valid⟩ ⟨column, small⟩).2.2

theorem chi_slot_lane {index : Fin 361} {round row : Nat}
    (shape : index.val = 15 * round + 10 + row) (valid : round < 24) (small : row < 5)
    (j : Nat) (position : j < 5) :
    (slots index)[j] = laneSlot (round + 1) ⟨5 * ((j + 2 * row) % 5) + row, by omega⟩ := by
  obtain ⟨index, bound⟩ := index
  simp only at shape
  subst shape
  exact Fin.ext ((chi_table ⟨round, valid⟩ ⟨row, small⟩).1 ⟨j, position⟩)

theorem chi_slot_five {index : Fin 361} {round row : Nat}
    (shape : index.val = 15 * round + 10 + row) (valid : round < 24) (small : row < 5) :
    (slots index)[5] = 30 := by
  obtain ⟨index, bound⟩ := index
  simp only at shape
  subst shape
  exact Fin.ext (chi_table ⟨round, valid⟩ ⟨row, small⟩).2.1

theorem chi_slot_six {index : Fin 361} {round row : Nat}
    (shape : index.val = 15 * round + 10 + row) (valid : round < 24) (small : row < 5) :
    (slots index)[6] = 30 := by
  obtain ⟨index, bound⟩ := index
  simp only at shape
  subst shape
  exact Fin.ext (chi_table ⟨round, valid⟩ ⟨row, small⟩).2.2

/-! ### The three call kinds, for every round -/

theorem input_entry (index : Fin 361) (state : LaneState) (j : Nat) (bound : j < 7) :
    (callInput index state)[j] = state ((slots index)[j]) := by
  simp only [callInput, Vector.getElem_ofFn, Fin.getElem_fin]

theorem parity_kind {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + column) (small : column < 5) :
    kindAt index.val = .columnParity := by
  have := index.isLt
  simp only [kindAt]
  split <;> first | rfl | (split <;> first | rfl | omega)

theorem theta_rho_kind {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + 5 + column) (small : column < 5) :
    kindAt index.val = .thetaRho := by
  simp only [kindAt]
  split
  · omega
  · split
    · omega
    · split
      · rfl
      · omega

theorem chi_kind {index : Fin 361} {round row : Nat}
    (shape : index.val = 15 * round + 10 + row) (small : row < 5) :
    kindAt index.val = .chi5 := by
  simp only [kindAt]
  split
  · omega
  · split
    · omega
    · split
      · omega
      · rfl

/-- Parity call `column` writes lane `j` of its column: unchanged, except the delayed iota on
    lane (0, 0). -/
theorem parity_step_lane {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + column) (valid : round < 25) (small : column < 5)
    (state : LaneState) {lane : Fin 25} {j : Nat} (position : j < 5)
    (hlane : lane.val = 5 * column + j) :
    microStep index state (laneSlot round lane) =
      if lane.val = 0 then state (laneSlot round lane) ^^^ roundConstant round
      else state (laneSlot round lane) := by
  obtain ⟨lane, bound⟩ := lane
  simp only at hlane
  subst hlane
  have kind := parity_kind shape small
  rw [← parity_slot_lane shape valid small j position,
    micro_step_slot index state (by rw [kind]; simp only [slotCount]; omega)]
  have round_eq : index.val / 15 = round := by omega
  have column_eq : index.val % 5 = column := by omega
  simp only [result, kind, round_eq, column_eq]
  interval_cases j <;> simp [input_entry]

/-- Parity call `column` writes C[column], the XOR of its column after the delayed iota. -/
theorem parity_step_column {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + column) (valid : round < 25) (small : column < 5)
    (state : LaneState) :
    microStep index state ⟨25 + column, by omega⟩ =
      (if column = 0 then
        state (laneSlot round ⟨5 * column, by omega⟩) ^^^ roundConstant round
      else state (laneSlot round ⟨5 * column, by omega⟩)) ^^^
        state (laneSlot round ⟨5 * column + 1, by omega⟩) ^^^
        state (laneSlot round ⟨5 * column + 2, by omega⟩) ^^^
        state (laneSlot round ⟨5 * column + 3, by omega⟩) ^^^
        state (laneSlot round ⟨5 * column + 4, by omega⟩) := by
  have kind := parity_kind shape small
  rw [← parity_slot_five shape valid small,
    micro_step_slot index state (by rw [kind]; simp only [slotCount]; omega)]
  have round_eq : index.val / 15 = round := by omega
  have column_eq : index.val % 5 = column := by omega
  simp only [result, kind, round_eq, column_eq, input_entry,
    parity_slot_lane shape valid small 0 (by decide), parity_slot_lane shape valid small 1 (by decide),
    parity_slot_lane shape valid small 2 (by decide), parity_slot_lane shape valid small 3 (by decide),
    parity_slot_lane shape valid small 4 (by decide)]
  rfl

/-- A parity call leaves every slot but its column and C[column] unchanged. -/
theorem parity_step_kept {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + column) (valid : round < 25) (small : column < 5)
    (state : LaneState) (physical : Fin 31)
    (lanes : ∀ j (position : j < 5), laneSlot round ⟨5 * column + j, by omega⟩ ≠ physical)
    (parity : (⟨25 + column, by omega⟩ : Fin 31) ≠ physical) :
    microStep index state physical = state physical := by
  apply micro_step_frame
  intro j active
  rw [parity_kind shape small] at active
  simp only [slotCount] at active
  by_cases lane : j < 5
  · rw [parity_slot_lane shape valid small j lane]
    exact lanes j lane
  · obtain rfl : j = 5 := by omega
    rw [parity_slot_five shape valid small]
    exact parity

/-- Theta+rho call `column` writes lane `j` of its column: rho of (lane ^ D[column]). -/
theorem theta_rho_step_lane {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + 5 + column) (valid : round < 24) (small : column < 5)
    (state : LaneState) {lane : Fin 25} {j : Nat} (position : j < 5)
    (hlane : lane.val = 5 * column + j) :
    microStep index state (laneSlot round lane) =
      rotLeft64 (state (laneSlot round lane) ^^^
        (state ⟨25 + (column + 4) % 5, by omega⟩ ^^^
          rotLeft64 (state ⟨25 + (column + 1) % 5, by omega⟩) 1))
        (rotations[column]'small)[j] := by
  obtain ⟨lane, bound⟩ := lane
  simp only at hlane
  subst hlane
  have kind := theta_rho_kind shape small
  rw [← theta_rho_slot_lane shape valid small j position,
    micro_step_slot index state (by rw [kind]; simp only [slotCount]; omega)]
  have column_eq : index.val % 5 = column := by omega
  simp only [result, kind, column_eq, Vector.getElem_ofFn, position, dite_true, input_entry,
    theta_rho_slot_five shape valid small, theta_rho_slot_six shape valid small, Fin.getElem_fin]

/-- A theta+rho call leaves every slot but its column unchanged (it writes C back as read). -/
theorem theta_rho_step_kept {index : Fin 361} {round column : Nat}
    (shape : index.val = 15 * round + 5 + column) (valid : round < 24) (small : column < 5)
    (state : LaneState) (physical : Fin 31)
    (lanes : ∀ j (position : j < 5), laneSlot round ⟨5 * column + j, by omega⟩ ≠ physical) :
    microStep index state physical = state physical := by
  have kind := theta_rho_kind shape small
  have readonly (j : Nat) (high : 5 ≤ j) (active : j < slotCount (kindAt index.val)) :
      microStep index state ((slots index)[j]'(lt_of_lt_of_le active (slot_count_bound _))) =
        state ((slots index)[j]'(lt_of_lt_of_le active (slot_count_bound _))) := by
    rw [micro_step_slot index state active]
    have short : ¬ j < 5 := by omega
    simp only [result, kind, Vector.getElem_ofFn, short, dite_false, Fin.getElem_fin, input_entry]
  by_cases five : (slots index)[5] = physical
  · subst five
    exact readonly 5 (by decide) (by rw [kind]; decide)
  by_cases six : (slots index)[6] = physical
  · subst six
    exact readonly 6 (by decide) (by rw [kind]; decide)
  apply micro_step_frame
  intro j active
  rw [kind] at active
  simp only [slotCount] at active
  by_cases lane : j < 5
  · rw [theta_rho_slot_lane shape valid small j lane]
    exact lanes j lane
  · obtain rfl | rfl : j = 5 ∨ j = 6 := by omega
    · exact five
    · exact six

/-- Chi call `row` writes lane `j` of its row: lane ^ (not next & next-but-one). -/
theorem chi_step_lane {index : Fin 361} {round row : Nat}
    (shape : index.val = 15 * round + 10 + row) (valid : round < 24) (small : row < 5)
    (state : LaneState) {lane : Fin 25} {j : Nat} (position : j < 5)
    (hlane : lane.val = 5 * ((j + 2 * row) % 5) + row) :
    microStep index state (laneSlot (round + 1) lane) =
      state (laneSlot (round + 1) lane) ^^^
        (not64 (state (laneSlot (round + 1) ⟨5 * (((j + 1) % 5 + 2 * row) % 5) + row, by omega⟩)) &&&
          state (laneSlot (round + 1) ⟨5 * (((j + 2) % 5 + 2 * row) % 5) + row, by omega⟩)) := by
  obtain ⟨lane, bound⟩ := lane
  simp only at hlane
  subst hlane
  have kind := chi_kind shape small
  rw [← chi_slot_lane shape valid small j position,
    micro_step_slot index state (by rw [kind]; simp only [slotCount]; omega)]
  simp only [result, kind, Vector.getElem_ofFn, position, dite_true, Fin.getElem_fin, input_entry,
    chi_slot_lane shape valid small _ (Nat.mod_lt _ (by decide : 0 < 5))]

/-- A chi call leaves every slot but its row unchanged. -/
theorem chi_step_kept {index : Fin 361} {round row : Nat}
    (shape : index.val = 15 * round + 10 + row) (valid : round < 24) (small : row < 5)
    (state : LaneState) (physical : Fin 31)
    (lanes : ∀ j, j < 5 → laneSlot (round + 1) ⟨5 * ((j + 2 * row) % 5) + row, by omega⟩ ≠ physical) :
    microStep index state physical = state physical := by
  apply micro_step_frame
  intro j active
  rw [chi_kind shape small] at active
  simp only [slotCount] at active
  rw [chi_slot_lane shape valid small j active]
  exact lanes j active

end Airbender.Keccak.Split.Call.Proofs

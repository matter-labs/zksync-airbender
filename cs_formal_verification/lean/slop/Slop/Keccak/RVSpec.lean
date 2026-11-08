module
public import Slop.Keccak.PhysicalStep
public import Slop.Keccak.Schedule
public import Slop.Deleg.KeccakClean
public import Slop.Deleg.KeccakSlots
public import Slop.Deleg.KeccakCalls
import all Init.Data.Array.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

/-! State-free agreement of the special5 circuit's call with the spec's `RV.Delegation.keccakSpecial5`. The circuit
    selects six physical slots by Clean's column-major `Controller.physicalLane`/`piSource`, the spec by the row-major
    `laneSlot`/`piSrc`; `physical_lane_slot` relates them once, for every round. Then, for every scheduled control, the
    controller's slots are `special5Slots`, `microValue` is `special5Op` on 64-bit lanes, `microStep` is
    `special5Step` (lanes as natural numbers) and the next control is `special5Next`. -/

namespace Airbender.Keccak.Proofs
open Spec RV.Delegation
set_option warningAsError true
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

/-- Clean's lane `5x + y` is the spec's lane `(x, y)`. -/
def specLane (i : Fin 25) : Fin 25 := lane ⟨i.val / 5, by omega⟩ ⟨i.val % 5, by omega⟩

theorem spec_lane_pi : ∀ i : Fin 25, specLane (Controller.piSource i) = piSrc (specLane i) := by decide

/-- The physical slot of Clean's lane `i` at round `r` is the spec's slot of lane `specLane i`. -/
theorem physical_lane_slot (r : Nat) (i : Fin 25) :
    Controller.physicalLane r i = (laneSlot r (specLane i)).val := by
  induction r generalizing i with
  | zero => simp only [Controller.physicalLane, laneSlot, specLane, lane]
  | succ r ih => rw [Controller.physicalLane, ih, spec_lane_pi, laneSlot_succ]

theorem physical_lane_xy (r : Nat) (x y : Fin 5) (i : Fin 25) (same : i.val = 5 * x.val + y.val) :
    Controller.physicalLane r i = (laneSlot r (lane x y)).val := by
  rw [physical_lane_slot]
  congr 2
  apply Fin.ext
  simp only [specLane, lane, same]
  omega

/-- The controller's six slots for a control in a run are the spec's `special5Slots`. -/
theorem rows_slots (mode : Fin 7) (x : Fin 5) (r : Nat)
    (valid : mode.val = 0 ∧ r ≤ 24 ∨ 0 < mode.val ∧ r < 24) (k : Fin 6) :
    (Controller.rows (Fin.ofNat 4096 (mode.val + 8 * x.val + 64 * r + 2048)))[k] =
      (special5Slots mode.val x r k).val := by
  have hm := mode.isLt
  have hx := x.isLt
  have hr : r ≤ 24 := by omega
  have key : (Fin.ofNat 4096 (mode.val + 8 * x.val + 64 * r + 2048)).val = mode.val + 8 * x.val + 64 * r + 2048 := by
    simp only [Fin.val_ofNat]; omega
  have m8 : (mode.val + 8 * x.val + 64 * r + 2048) % 8 = mode.val := by omega
  have x8 : (mode.val + 8 * x.val + 64 * r + 2048) / 8 % 8 = x.val := by omega
  have r64 : (mode.val + 8 * x.val + 64 * r + 2048) / 64 % 32 = r := by omega
  have big : 2048 ≤ mode.val + 8 * x.val + 64 * r + 2048 := by omega
  simp only [Controller.rows, key, m8, x8, r64, hx, ↓reduceIte]
  fin_cases mode
  · have h24 : r ≤ 24 := by omega
    simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, true_and, h24, big, and_self, ↓reduceIte]
    fin_cases k
    all_goals simp only [special5Slots, h24, true_and, true_or, ↓reduceIte, Vector.getElem_ofFn, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, slot, scratch, Fin.val_castLE, Fin.val_castSucc]
    all_goals first
      | rfl
      | (apply physical_lane_xy; simp only [Fin.val_natCast, Fin.val_ofNat, Fin.isValue]; omega)
  all_goals have h24 : r < 24 := by simp at valid; omega
  all_goals simp only [Fin.isValue, Fin.reduceFinMk, Fin.val_succ, h24, and_true, ↓reduceIte]
  all_goals fin_cases k
  all_goals simp only [special5Slots, h24, true_and, or_true, ↓reduceIte, Vector.getElem_ofFn, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, slot, scratch, Fin.val_castLE, Fin.val_castSucc,
    Nat.reduceAdd, Nat.one_lt_ofNat, Nat.ofNat_pos, Nat.lt_irrefl, OfNat.ofNat_ne_zero, false_and, false_or,
    and_false, or_false, Vector.getElem_mk]
  all_goals first
    | rfl
    | (apply physical_lane_xy; simp only [Fin.val_natCast, Fin.val_ofNat, Fin.isValue]; omega)
    | (fin_cases x <;> rfl)

theorem big_ne_fin25 (a : Fin 25) {k : Nat} (h : 25 ≤ k) : (k = a.val) ↔ False := ⟨fun e => by omega, False.elim⟩

theorem special5_slots_injective (mode : Fin 7) (x : Fin 5) (r : Nat)
    (valid : mode.val = 0 ∧ r ≤ 24 ∨ 0 < mode.val ∧ r < 24) :
    Function.Injective (special5Slots mode.val x r) := by
  intro a b same
  have values := congrArg Fin.val same
  clear same
  revert values
  fin_cases mode
  · have h24 : r ≤ 24 := by omega
    fin_cases a <;> fin_cases b
    all_goals simp [special5Slots, slot, scratch, h24, laneSlot_val_eq, lane_eq_iff, slot_ne_scratch,
      scratch_ne_slot, slot_ne_25, ne_slot_25, fin25_val_ne, big_ne_fin25]
  all_goals have h24 : r < 24 := by simp at valid; omega
  all_goals fin_cases a <;> fin_cases b
  all_goals simp [special5Slots, slot, scratch, h24, laneSlot_val_eq, lane_eq_iff, slot_ne_scratch,
    scratch_ne_slot, slot_ne_25, ne_slot_25, fin25_val_ne, big_ne_fin25]

theorem foldl_set_hit (sl : Fin 6 → Fin 31) (out : Fin 6 → Lane) (S : Vector Lane 31)
    (injective : Function.Injective sl) (k : Fin 6) :
    ((List.finRange 6).foldl (fun S i => S.set (sl i) (out i)) S)[sl k] = out k := by
  have ne (a b : Fin 6) (different : a ≠ b) : (sl a).val ≠ (sl b).val := fun h => different (injective (Fin.ext h))
  rw [finRange6_foldl]
  fin_cases k <;> simp [Vector.getElem_set, ne]

theorem foldl_set_miss (sl : Fin 6 → Fin 31) (out : Fin 6 → Lane) (S : Vector Lane 31) (j : Fin 31)
    (miss : ∀ k, sl k ≠ j) :
    ((List.finRange 6).foldl (fun S i => S.set (sl i) (out i)) S)[j] = S[j] := by
  have ne (k : Fin 6) : (sl k).val ≠ j.val := fun h => miss k (Fin.ext h)
  rw [finRange6_foldl]
  simp [Vector.getElem_set, ne]

theorem round_constant_nat : ∀ k : Fin 24, (Specs.Keccak256.roundConstants[k.val]).toNat = (RC k).toNat := by
  decide

theorem rho_rotation_val (x : Fin 5) : ∀ y : Fin 5, ((rhoRotations[x.val])[y.val]).val = rhoOffset x y := by
  revert x
  decide

/-- The circuit's micro-operation on six 64-bit lanes is the spec's `special5Op`. -/
theorem micro_value_spec (mode : Fin 7) (x : Fin 5) (round : Fin 32) (bound : round.val < 25)
    (v : Fin 6 → Lane) (k : Fin 6) :
    microValue ⟨mode, x, round⟩ (fun j => (v j).toNat) k = (special5Op mode.val x round.val v k).toNat := by
  fin_cases mode
  · by_cases first : x = 0
    · subst first
      by_cases positive : 0 < round.val
      · have index : (round.val - 1) % 24 = round.val - 1 := Nat.mod_eq_of_lt (by omega)
        have rc : (Specs.Keccak256.roundConstants[round.val - 1]'(by omega)).toNat =
            (delayedRC round.val).toNat := by
          rw [delayedRC, dite_eq_left ⟨positive, by omega⟩]
          exact round_constant_nat ⟨round.val - 1, by omega⟩
        fin_cases k
        all_goals simp [microValue, iotaValue, special5Op, positive, BitVec.toNat_xor, index, rc]
      · have zero : round.val = 0 := by omega
        fin_cases k
        all_goals simp [microValue, iotaValue, special5Op, zero, delayedRC, BitVec.toNat_xor]
    · fin_cases k
      all_goals simp [microValue, iotaValue, special5Op, first, BitVec.toNat_xor]
  rotate_left 3
  · have r0 := rho_rotation_val x ⟨0, by decide⟩
    have r1 := rho_rotation_val x ⟨1, by decide⟩
    have r2 := rho_rotation_val x ⟨2, by decide⟩
    have r3 := rho_rotation_val x ⟨3, by decide⟩
    have r4 := rho_rotation_val x ⟨4, by decide⟩
    simp only [Fin.isValue] at r0 r1 r2 r3 r4
    fin_cases k
    all_goals simp [microValue, special5Op, rotLeft64_toNat, r0, r1, r2, r3, r4, -BitVec.toNat_rotateLeft]
  all_goals fin_cases k
  all_goals simp [microValue, special5Op, BitVec.toNat_xor, BitVec.toNat_and, rotLeft64_toNat, not64_toNat]

/-- The spec's next control is the circuit's `nextPacked`. -/
theorem next_packed (c : ControlState) :
    (special5Next c.mode.val c.iteration.val c.round.val).1 +
      8 * (special5Next c.mode.val c.iteration.val c.round.val).2.1 +
      64 * (special5Next c.mode.val c.iteration.val c.round.val).2.2 = c.nextPacked := by
  obtain ⟨mode, x, round⟩ := c
  fin_cases mode <;> fin_cases x <;> simp [special5Next, ControlState.nextPacked]

/-- Every control of the pinned 649-call schedule is a piece of a run (`special5Slots`'s condition). -/
theorem schedule_valid : ∀ call : Fin 649,
    (scheduleControl ⟨call.val, by omega⟩).mode.val = 0 ∧ (scheduleControl ⟨call.val, by omega⟩).round.val ≤ 24 ∨
      0 < (scheduleControl ⟨call.val, by omega⟩).mode.val ∧ (scheduleControl ⟨call.val, by omega⟩).round.val < 24 := by
  intro call
  have := call.isLt
  dsimp only [scheduleControl]
  split_ifs <;> omega

theorem slot_indices_spec (call : Fin 649) (k : Fin 6) :
    (slotIndices call)[k] = (special5Slots (scheduleControl ⟨call.val, by omega⟩).mode.val
      (scheduleControl ⟨call.val, by omega⟩).iteration (scheduleControl ⟨call.val, by omega⟩).round.val k).val :=
  rows_slots _ _ _ (schedule_valid call) k

/-- One scheduled call: the spec's `special5Step` on 64-bit lanes is the circuit's `microStep` on their values. -/
theorem special5_step_nat (call : Fin 649) (L : Vector Lane 31) (j : Fin 31) :
    (special5Step (scheduleControl ⟨call.val, by omega⟩).mode.val (scheduleControl ⟨call.val, by omega⟩).iteration
      (scheduleControl ⟨call.val, by omega⟩).round.val L)[j].toNat = microStep call (fun l => L[l].toNat) j := by
  have valid := schedule_valid call
  have bound : (scheduleControl ⟨call.val, by omega⟩).round.val < 25 := by omega
  have injective := special5_slots_injective _ (scheduleControl ⟨call.val, by omega⟩).iteration _ valid
  have indices := slot_indices_spec call
  rw [micro_step_get]
  have reads : (fun lane : Fin 6 => (fun l : Fin 31 => L[l].toNat)
        ⟨(slotIndices call)[lane], Controller.Proofs.rows_bound _ lane⟩) =
      fun lane => (L[special5Slots (scheduleControl ⟨call.val, by omega⟩).mode.val
        (scheduleControl ⟨call.val, by omega⟩).iteration (scheduleControl ⟨call.val, by omega⟩).round.val lane]).toNat := by
    funext lane
    simp only [Fin.getElem_fin, indices lane]
  rw [reads]
  by_cases present : (slotIndices call).toList.idxOf j.val < 6
  · rw [dite_eq_left present]
    let k : Fin 6 := ⟨_, present⟩
    have atIndex : (slotIndices call)[k] = j.val := by
      have found := List.getElem_idxOf (xs := (slotIndices call).toList) (x := j.val)
        (by simpa only [Vector.length_toList] using present)
      exact (by simpa only [Vector.getElem_toList] using found :
        (slotIndices call)[List.idxOf j.val (slotIndices call).toList] = j.val)
    have same : special5Slots (scheduleControl ⟨call.val, by omega⟩).mode.val
        (scheduleControl ⟨call.val, by omega⟩).iteration (scheduleControl ⟨call.val, by omega⟩).round.val k = j :=
      Fin.ext ((indices k).symm.trans atIndex)
    have hit := foldl_set_hit _ (special5Op (scheduleControl ⟨call.val, by omega⟩).mode.val
      (scheduleControl ⟨call.val, by omega⟩).iteration (scheduleControl ⟨call.val, by omega⟩).round.val
      fun i => L[special5Slots (scheduleControl ⟨call.val, by omega⟩).mode.val
        (scheduleControl ⟨call.val, by omega⟩).iteration (scheduleControl ⟨call.val, by omega⟩).round.val i])
      L injective k
    simp only [same] at hit
    simp only [special5Step]
    simp only [Fin.getElem_fin] at hit ⊢
    rw [hit]
    exact (micro_value_spec _ _ _ bound _ k).symm
  · rw [dite_eq_right present]
    have miss : ∀ k, special5Slots (scheduleControl ⟨call.val, by omega⟩).mode.val
        (scheduleControl ⟨call.val, by omega⟩).iteration (scheduleControl ⟨call.val, by omega⟩).round.val k ≠ j := by
      intro k same
      apply present
      have member : j.val ∈ (slotIndices call).toList := by
        rw [← same, ← indices k]
        simp
      simpa only [Vector.length_toList] using List.idxOf_lt_length_of_mem member
    simp only [special5Step]
    rw [foldl_set_miss _ _ _ j miss]

end Airbender.Keccak.Proofs

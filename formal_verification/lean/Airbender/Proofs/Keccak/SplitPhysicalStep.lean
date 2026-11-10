import Airbender.Proofs.Keccak.SplitPhysicalSnapshot

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- Exact Sail word effects give the unchanged complete physical lane step.
The unused padding lane needs no initialized memory cell. -/
theorem physical_step_of_words (index : Fin 361) (pointer : BitVec 32)
    {before after : State} {initial final : LaneState} (input : Vector Nat 7)
    (inputBounds : ∀ lane : Fin 7, input[lane] < 2 ^ 64)
    (beforeSnapshot : PhysicalSnapshot before pointer initial)
    (afterSnapshot : PhysicalSnapshot after pointer final)
    (reads : ∀ lane : Fin 7, lane.val < slotCount (kindAt index.val) →
      (laneCell pointer (slots index)[lane] false).read before = .ok (half input[lane] false) before ∧
      (laneCell pointer (slots index)[lane] true).read before = .ok (half input[lane] true) before)
    (written : ∀ lane : Fin 7, lane.val < slotCount (kindAt index.val) → ∀ high : Bool,
      (laneCell pointer (slots index)[lane] high).read after = .ok (half (result index input)[lane] high) after)
    (frame : ∀ (physical : Fin 31) (high : Bool),
      (∀ lane : Fin 7, lane.val < slotCount (kindAt index.val) → (slots index)[lane] ≠ physical) →
      ∀ value : BitVec 32,
        (laneCell pointer physical high).read before = .ok value before →
        (laneCell pointer physical high).read after = .ok value after) :
    final = microStep index initial := by
  let source : Vector Nat 7 := Vector.ofFn fun lane : Fin 7 => initial (slots index)[lane]
  have agree (lane : Fin 7) (live : lane.val < slotCount (kindAt index.val)) : input[lane] = source[lane] := by
    have observed := beforeSnapshot.2 (slots index)[lane] (active_slot_bound index lane live)
    have low := (EStateM.Result.ok.inj ((reads lane live).1.symm.trans (observed.2 false))).1
    have high := (EStateM.Result.ok.inj ((reads lane live).2.symm.trans (observed.2 true))).1
    simpa only [source, Fin.getElem_fin, Vector.getElem_ofFn] using
      lane_eq_of_halves (inputBounds lane) observed.1 low high
  have outputs := result_live_congr index input source agree
  funext physical
  let slot := (slots index).toList.idxOf physical
  change final physical = if live : slot < slotCount (kindAt index.val) then
    (result index source)[slot]'(lt_of_lt_of_le live (slot_count_bound _)) else initial physical
  by_cases live : slot < slotCount (kindAt index.val)
  · rw [dif_pos live]
    have bound : slot < 7 := lt_of_lt_of_le live (slot_count_bound _)
    have found : (slots index)[slot] = physical := by
      simpa only [Vector.getElem_toList] using List.getElem_idxOf
        (show (slots index).toList.idxOf physical < (slots index).toList.length by simpa using bound)
    have valid : physical.val < 30 := by
      simpa only [Fin.getElem_fin, found] using active_slot_bound index ⟨slot, bound⟩ live
    have observed := afterSnapshot.2 physical valid
    have lowRead : (laneCell pointer physical false).read after =
        .ok (half (result index input)[slot] false) after := by
      simpa only [Fin.getElem_fin, found] using written ⟨slot, bound⟩ live false
    have highRead : (laneCell pointer physical true).read after =
        .ok (half (result index input)[slot] true) after := by
      simpa only [Fin.getElem_fin, found] using written ⟨slot, bound⟩ live true
    have low := (EStateM.Result.ok.inj ((observed.2 false).symm.trans lowRead)).1
    have high := (EStateM.Result.ok.inj ((observed.2 true).symm.trans highRead)).1
    have value := lane_eq_of_halves observed.1 (result_lane_bound index input inputBounds ⟨slot, bound⟩) low high
    exact value.trans (by simpa only [Fin.getElem_fin] using outputs ⟨slot, bound⟩ live)
  · rw [dif_neg live]
    by_cases padding : physical.val = 30
    · have same : physical = (30 : Fin 31) := Fin.ext padding
      rw [same, beforeSnapshot.1, afterSnapshot.1]
    · have valid : physical.val < 30 := by have := physical.isLt; omega
      have untouched (lane : Fin 7) (active : lane.val < slotCount (kindAt index.val)) : (slots index)[lane] ≠ physical := by
        intro same
        have fullMember : physical ∈ (slots index).toList := by
          apply List.mem_iff_getElem.mpr
          refine ⟨lane.val, by simp, ?_⟩
          simpa only [Vector.getElem_toList, Fin.getElem_fin] using same
        have member : physical ∈ (slots index).toList.take (slotCount (kindAt index.val)) := by
          apply List.mem_iff_getElem.mpr
          refine ⟨lane.val, ?_, ?_⟩
          · simpa only [List.length_take, Vector.length_toList,
              Nat.min_eq_left (slot_count_bound _)] using active
          · simpa only [List.getElem_take, Vector.getElem_toList, Fin.getElem_fin] using same
        exact live ((List.mem_take_iff_idxOf_lt fullMember).mp member)
      have first := beforeSnapshot.2 physical valid
      have second := afterSnapshot.2 physical valid
      have lowRead := frame physical false untouched _ (first.2 false)
      have highRead := frame physical true untouched _ (first.2 true)
      have low := (EStateM.Result.ok.inj ((second.2 false).symm.trans lowRead)).1
      have high := (EStateM.Result.ok.inj ((second.2 true).symm.trans highRead)).1
      exact lane_eq_of_halves second.1 first.1 low high

end Airbender.Keccak.Split.Call.Proofs

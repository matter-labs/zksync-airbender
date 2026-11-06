import Slop.KeccakSplit.Reference.PhysicalSnapshot

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- The padding slot is never a live slot of a call. -/
theorem padding_not_live (index : Fin 361) :
    ¬ (slots index).toList.idxOf (30 : Fin 31) < slotCount (kindAt index.val) := by
  intro live
  have bound : (slots index).toList.idxOf (30 : Fin 31) < 7 :=
    lt_of_lt_of_le live (slot_count_bound _)
  have found : (slots index)[(slots index).toList.idxOf (30 : Fin 31)] = (30 : Fin 31) := by
    simpa only [Vector.getElem_toList] using List.getElem_idxOf
      (show (slots index).toList.idxOf (30 : Fin 31) < (slots index).toList.length by simpa using bound)
  have small := active_slot_bound index ⟨_, bound⟩ live
  simp only [Fin.getElem_fin, found] at small
  exact absurd small (by decide)

/-- One call's Sail effects carry a complete physical snapshot to the next state:
the lanes after the call are `microStep` of the lanes before. -/
theorem snapshot_step (index : Fin 361) (pointer : BitVec 32)
    (aligned : pointer.toNat % 256 = 0) {before after : State} {lanes : LaneState}
    (snapshot : PhysicalSnapshot before pointer lanes) (input : Vector Nat 7)
    (reads : ∀ lane : Fin 7, lane.val < slotCount (kindAt index.val) →
      input[lane] < 2 ^ 64 ∧
      (laneCell pointer (slots index)[lane] false).read before = .ok (half input[lane] false) before ∧
      (laneCell pointer (slots index)[lane] true).read before = .ok (half input[lane] true) before)
    (execution : AtomicWrites (writes index pointer (result index input)) before after) :
    PhysicalSnapshot after pointer (microStep index lanes) := by
  let source : Vector Nat 7 := Vector.ofFn fun lane : Fin 7 => lanes (slots index)[lane]
  have sourceBounds (lane : Fin 7) : source[lane] < 2 ^ 64 := by
    simp only [source, Fin.getElem_fin, Vector.getElem_ofFn]
    by_cases padding : ((slots index)[lane.val]).val = 30
    · have same : (slots index)[lane.val] = (30 : Fin 31) := Fin.ext padding
      rw [same, snapshot.1]
      decide
    · exact (snapshot.2 _ (by have := ((slots index)[lane.val]).isLt; omega)).1
  have agree (lane : Fin 7) (live : lane.val < slotCount (kindAt index.val)) :
      input[lane] = source[lane] := by
    have observed := snapshot.2 (slots index)[lane] (active_slot_bound index lane live)
    have low := (EStateM.Result.ok.inj ((reads lane live).2.1.symm.trans (observed.2 false))).1
    have high := (EStateM.Result.ok.inj ((reads lane live).2.2.symm.trans (observed.2 true))).1
    simpa only [source, Fin.getElem_fin, Vector.getElem_ofFn] using
      lane_eq_of_halves (reads lane live).1 observed.1 low high
  have outputs := result_live_congr index input source agree
  have sourceExecution : AtomicWrites (writes index pointer (result index source)) before after := by
    rw [← writes_live_congr index pointer _ _ outputs]
    exact execution
  have unfolded (physical : Fin 31) : microStep index lanes physical =
      if live : (slots index).toList.idxOf physical < slotCount (kindAt index.val) then
        (result index source)[(slots index).toList.idxOf physical]'(lt_of_lt_of_le live (slot_count_bound _))
      else lanes physical := rfl
  refine ⟨?_, ?_⟩
  · rw [unfolded, dite_eq_right (padding_not_live index)]
    exact snapshot.1
  · intro physical valid
    rw [unfolded]
    by_cases live : (slots index).toList.idxOf physical < slotCount (kindAt index.val)
    · rw [dite_eq_left live]
      have bound : (slots index).toList.idxOf physical < 7 := lt_of_lt_of_le live (slot_count_bound _)
      have found : (slots index)[(slots index).toList.idxOf physical] = physical := by
        simpa only [Vector.getElem_toList] using List.getElem_idxOf
          (show (slots index).toList.idxOf physical < (slots index).toList.length by simpa using bound)
      refine ⟨result_lane_bound index source sourceBounds ⟨_, bound⟩, fun high => ?_⟩
      have read := written_lane_reads index pointer aligned (result index source) sourceExecution
        ⟨_, bound⟩ live high
      simpa only [Fin.getElem_fin, found] using read
    · rw [dite_eq_right live]
      have untouched (lane : Fin 7) (active : lane.val < slotCount (kindAt index.val)) :
          (slots index)[lane] ≠ physical := by
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
      have observed := snapshot.2 physical valid
      exact ⟨observed.1, fun high => unwritten_lane_frame index pointer aligned (result index source)
        sourceExecution physical high untouched _ (observed.2 high)⟩

end Airbender.Keccak.Split.Call.Proofs

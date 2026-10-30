import Airbender.Proofs.Keccak.SplitCallDestinations
import Airbender.Proofs.Keccak.SplitCallValues
import Airbender.Proofs.Keccak.SplitScheduleControl
import Airbender.Proofs.Trace.InterleavedProjection

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false

private theorem control_word_bound (index : Fin 361) : controlAt index.val < 2 ^ 32 := by
  have indexBound := index.isLt
  by_cases last : index.val = 360
  · norm_num [controlAt, last, encode, Kind.mode]
  · unfold controlAt
    rw [if_neg last]
    cases kindAt index.val <;> simp only [encode, Kind.mode]
    all_goals have remainder := Nat.mod_lt index.val (by decide : 0 < 5)
    all_goals norm_num only [Nat.reducePow]
    all_goals omega

/-- The reference control register identifies one exact blessed call index. -/
theorem arguments_index_injective {one two : Fin 361} {before : State}
    (first : ArgumentsAt one.val before) (second : ArgumentsAt two.val before) : one = two := by
  obtain ⟨firstControl, _, firstRead, _, firstWord, _, _⟩ := first
  obtain ⟨secondControl, _, secondRead, _, secondWord, _, _⟩ := second
  have bits := (EStateM.Result.ok.inj (firstRead.symm.trans secondRead)).1
  rw [firstWord, secondWord] at bits
  have numeric := congrArg BitVec.toNat bits
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (control_word_bound one),
    Nat.mod_eq_of_lt (control_word_bound two)] at numeric
  exact Split.Proofs.control_injective numeric

/-- Every live reference lane half occurs in the complete declared write list. -/
theorem written_lane_member (index : Fin 361) (pointer : BitVec 32) (output : Vector Nat 7)
    (lane : Fin 7) (live : lane.val < slotCount (kindAt index.val)) (high : Bool) :
    (laneCell pointer (slots index)[lane] high, half output[lane] high) ∈ writes index pointer output := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨lane.val, List.mem_range.mpr live, ?_⟩
  simp only [lane.isLt, ↓reduceDIte]
  cases high <;> simp only [Fin.getElem_fin, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- An actual atomic reference call gives the exact final word of each touched lane half. -/
theorem written_lane_reads (index : Fin 361) (pointer : BitVec 32)
    (aligned : pointer.toNat % 256 = 0) (output : Vector Nat 7) {before after : State}
    (execution : AtomicWrites (writes index pointer output) before after)
    (lane : Fin 7) (live : lane.val < slotCount (kindAt index.val)) (high : Bool) :
    (laneCell pointer (slots index)[lane] high).read after =
      .ok (half output[lane] high) after := by
  exact atomic_writes_reads execution (writes_aligned index pointer aligned output)
    (writes_distinct index pointer aligned output) (written_lane_member index pointer output lane live high)
    (by simp only [laneCell, ne_eq, reduceCtorEq, not_false_eq_true])

/-- A physical lane outside the declared live slots retains each exact Sail word. -/
theorem unwritten_lane_frame (index : Fin 361) (pointer : BitVec 32)
    (aligned : pointer.toNat % 256 = 0) (output : Vector Nat 7) {before after : State}
    (execution : AtomicWrites (writes index pointer output) before after)
    (physical : Fin 31) (high : Bool)
    (untouched : ∀ lane : Fin 7, lane.val < slotCount (kindAt index.val) → (slots index)[lane] ≠ physical)
    (value : BitVec 32) (read : (laneCell pointer physical high).read before = .ok value before) :
    (laneCell pointer physical high).read after = .ok value after := by
  apply atomic_writes_frame execution (writes_aligned index pointer aligned output)
    (lane_cell_aligned pointer aligned physical high) _ read
  intro entry member same
  rcases List.mem_append.mp member with register | memory
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at register
    rcases register with rfl | rfl <;> cases same
  · obtain ⟨lane, present, included⟩ := List.mem_flatMap.mp memory
    split_ifs at included with valid
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl
      · have equal := @lane_cell_injective pointer aligned (physical, high) ((slots index)[lane], false) same
        exact untouched ⟨lane, valid⟩ (List.mem_range.mp present) (congrArg Prod.fst equal).symm
      · have equal := @lane_cell_injective pointer aligned (physical, high) ((slots index)[lane], true) same
        exact untouched ⟨lane, valid⟩ (List.mem_range.mp present) (congrArg Prod.fst equal).symm
    · cases included

end Airbender.Keccak.Split.Call.Proofs

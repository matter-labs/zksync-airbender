module
public import Slop.KeccakSplit.Reference.Executions
public import Slop.KeccakSplit.Trace.RVAtomicWrites
public import Human.Trace.Workers.KeccakSplit.RVCall
public import Human.Trace.Workers.Keccak.RVCall

@[expose] public section

/-! RV twins of `CallMemoryProjection.lean` (lane reads/frame), `PhysicalSnapshot.lean`, `SnapshotStep.lean`,
    `Chain.lean` and `Executions.lean`: the 361 documented split calls executed on `RV.State`s (`Call.RVExecutesAt`)
    carry the x11 pointer and a physical lane snapshot along `microStep`, and so write Clean's Keccak-f[1600]
    permutation. RAM cells include the shadow RAM below `ROM_END`. -/

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536

/-- RV sibling of `PhysicalSnapshot`. -/
def RVPhysicalSnapshot (state : RV.State) (pointer : BitVec 32) (lanes : LaneState) : Prop :=
  lanes 30 = 0 ∧ ∀ physical : Fin 31, physical.val < 30 →
    lanes physical < 2 ^ 64 ∧ ∀ high : Bool,
      (laneCell pointer physical high).readRV state = some (half (lanes physical) high)

theorem rv_written_lane_reads (index : Fin 361) (pointer : BitVec 32)
    (aligned : pointer.toNat % 256 = 0) (output : Vector Nat 7) {before after : RV.State}
    (execution : RVAtomicWrites (writes index pointer output) before after)
    (lane : Fin 7) (live : lane.val < slotCount (kindAt index.val)) (high : Bool) :
    (laneCell pointer (slots index)[lane] high).readRV after = some (half output[lane] high) :=
  rv_atomic_writes_reads execution (writes_aligned index pointer aligned output)
    (writes_distinct index pointer aligned output) (written_lane_member index pointer output lane live high)
    (by simp only [laneCell, ne_eq, reduceCtorEq, not_false_eq_true])

theorem rv_unwritten_lane_frame (index : Fin 361) (pointer : BitVec 32)
    (aligned : pointer.toNat % 256 = 0) (output : Vector Nat 7) {before after : RV.State}
    (execution : RVAtomicWrites (writes index pointer output) before after)
    (physical : Fin 31) (high : Bool)
    (untouched : ∀ lane : Fin 7, lane.val < slotCount (kindAt index.val) → (slots index)[lane] ≠ physical)
    (value : BitVec 32) (read : (laneCell pointer physical high).readRV before = some value) :
    (laneCell pointer physical high).readRV after = some value := by
  apply rv_atomic_writes_frame execution (writes_aligned index pointer aligned output)
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

theorem rv_snapshot_step (index : Fin 361) (pointer : BitVec 32)
    (aligned : pointer.toNat % 256 = 0) {before after : RV.State} {lanes : LaneState}
    (snapshot : RVPhysicalSnapshot before pointer lanes) (input : Vector Nat 7)
    (reads : ∀ lane : Fin 7, lane.val < slotCount (kindAt index.val) →
      input[lane] < 2 ^ 64 ∧
      (laneCell pointer (slots index)[lane] false).readRV before = some (half input[lane] false) ∧
      (laneCell pointer (slots index)[lane] true).readRV before = some (half input[lane] true))
    (execution : RVAtomicWrites (writes index pointer (result index input)) before after) :
    RVPhysicalSnapshot after pointer (microStep index lanes) := by
  let source : Vector Nat 7 := Vector.ofFn fun lane : Fin 7 => lanes (slots index)[lane]
  have agree (lane : Fin 7) (live : lane.val < slotCount (kindAt index.val)) :
      input[lane] = source[lane] := by
    have observed := snapshot.2 (slots index)[lane] (active_slot_bound index lane live)
    have low := Option.some.inj ((reads lane live).2.1.symm.trans (observed.2 false))
    have high := Option.some.inj ((reads lane live).2.2.symm.trans (observed.2 true))
    simpa only [source, Fin.getElem_fin, Vector.getElem_ofFn] using
      lane_eq_of_halves (reads lane live).1 observed.1 low high
  have sourceBounds (lane : Fin 7) : source[lane] < 2 ^ 64 := by
    simp only [source, Fin.getElem_fin, Vector.getElem_ofFn]
    by_cases padding : ((slots index)[lane.val]).val = 30
    · have same : (slots index)[lane.val] = (30 : Fin 31) := Fin.ext padding
      rw [same, snapshot.1]
      decide
    · exact (snapshot.2 _ (by have := ((slots index)[lane.val]).isLt; omega)).1
  have outputs := result_live_congr index input source agree
  have sourceExecution : RVAtomicWrites (writes index pointer (result index source)) before after := by
    rw [← writes_live_congr index pointer _ _ outputs]
    exact execution
  have unfolded (physical : Fin 31) : microStep index lanes physical =
      if live : (slots index).toList.idxOf physical < slotCount (kindAt index.val) then
        (result index source)[(slots index).toList.idxOf physical]'(lt_of_lt_of_le live (slot_count_bound _))
      else lanes physical := by rfl
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
      have read := rv_written_lane_reads index pointer aligned (result index source) sourceExecution
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
      exact ⟨observed.1, fun high => rv_unwritten_lane_frame index pointer aligned (result index source)
        sourceExecution physical high untouched _ (observed.2 high)⟩

theorem rv_executes_pointer {index : Fin 361} {before after : RV.State} {pointer : BitVec 32}
    (execution : RVExecutesAt index before after)
    (read : (Cell.register 11).readRV before = some pointer) :
    pointer.toNat % 256 = 0 ∧ (Cell.register 11).readRV after = some pointer := by
  obtain ⟨called, input, arguments, calledRead, _, atomic⟩ := execution
  obtain ⟨_, argument, _, argumentRead, _, aligned⟩ := arguments
  have same := Option.some.inj (calledRead.symm.trans read)
  have sameArgument := Option.some.inj (argumentRead.symm.trans read)
  subst same
  subst sameArgument
  refine ⟨aligned, ?_⟩
  exact rv_atomic_writes_reads atomic (writes_aligned index _ aligned _)
    (writes_distinct index _ aligned _) (by simp [writes]) (by decide)

theorem rv_executes_snapshot {index : Fin 361} {before after : RV.State} {pointer : BitVec 32}
    {lanes : LaneState} (execution : RVExecutesAt index before after)
    (read : (Cell.register 11).readRV before = some pointer)
    (snapshot : RVPhysicalSnapshot before pointer lanes) :
    RVPhysicalSnapshot after pointer (microStep index lanes) := by
  have aligned := (rv_executes_pointer execution read).1
  obtain ⟨called, input, _, calledRead, reads, atomic⟩ := execution
  have same := Option.some.inj (calledRead.symm.trans read)
  subst same
  exact rv_snapshot_step index called aligned snapshot input reads atomic

theorem rv_initial_snapshot {state : RV.State} {pointer : BitVec 32}
    (reads : ∀ (slot : Fin 30) (high : Bool), ∃ value : BitVec 32,
      (laneCell pointer ⟨slot.val, by omega⟩ high).readRV state = some value) :
    ∃ lanes : LaneState, RVPhysicalSnapshot state pointer lanes := by
  choose value hvalue using reads
  refine ⟨fun physical => if valid : physical.val < 30 then
    (value ⟨physical.val, valid⟩ false).toNat + 2 ^ 32 * (value ⟨physical.val, valid⟩ true).toNat
    else 0, by simp, ?_⟩
  intro physical valid
  have lowBound := (value ⟨physical.val, valid⟩ false).isLt
  have highBound := (value ⟨physical.val, valid⟩ true).isLt
  simp only [dite_eq_left valid, half_combine]
  refine ⟨by omega, fun high => ?_⟩
  cases high
  · exact hvalue ⟨physical.val, valid⟩ false
  · exact hvalue ⟨physical.val, valid⟩ true

theorem rv_chain_of_executions (states : Fin 362 → RV.State) (pointer : BitVec 32)
    (exec : ∀ index : Fin 361, RVExecutesAt index (states index.castSucc) (states index.succ))
    (pointerRead : (Cell.register 11).readRV (states 0) = some pointer)
    (initialReads : ∀ (slot : Fin 30) (high : Bool), ∃ value : BitVec 32,
      (laneCell pointer ⟨slot.val, by omega⟩ high).readRV (states 0) = some value) :
    pointer.toNat % 256 = 0 ∧ ∃ lanes : Fin 362 → LaneState,
      (∀ index : Fin 362, (Cell.register 11).readRV (states index) = some pointer) ∧
      (∀ index : Fin 362, RVPhysicalSnapshot (states index) pointer (lanes index)) ∧
      (∀ index : Fin 361, lanes index.succ = microStep index (lanes index.castSucc)) := by
  obtain ⟨initial, initialSnapshot⟩ := rv_initial_snapshot initialReads
  have carried (count : Nat) (bound : count < 362) :
      (Cell.register 11).readRV (states ⟨count, bound⟩) = some pointer ∧
      RVPhysicalSnapshot (states ⟨count, bound⟩) pointer (chainLanes initial count) := by
    induction count with
    | zero => exact ⟨pointerRead, initialSnapshot⟩
    | succ count ih =>
      obtain ⟨read, snapshot⟩ := ih (by omega)
      have execution := exec ⟨count, by omega⟩
      have call : Fin.ofNat 361 count = (⟨count, by omega⟩ : Fin 361) :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      exact ⟨(rv_executes_pointer execution read).2, by
        rw [chainLanes, call]
        exact rv_executes_snapshot execution read snapshot⟩
  refine ⟨(rv_executes_pointer (exec 0) pointerRead).1, fun index => chainLanes initial index.val,
    fun index => (carried index.val index.isLt).1, fun index => (carried index.val index.isLt).2, ?_⟩
  intro index
  have call : Fin.ofNat 361 index.val = index := Fin.ext (Nat.mod_eq_of_lt index.isLt)
  simp only [Fin.val_succ, Fin.val_castSucc, chainLanes, call]

theorem rv_lanes_at_of_snapshot {state : RV.State} {pointer : BitVec 32} {lanes : LaneState}
    (snapshot : RVPhysicalSnapshot state pointer lanes) :
    Keccak.Permutation.RVLanesAt state pointer (logicalLanes 0 lanes) := by
  intro lane
  have observed := snapshot.2 (initialSlot lane) (initial_slot_bound lane)
  have value : (logicalLanes 0 lanes)[lane] = lanes (initialSlot lane) := by
    simp only [logicalLanes, Fin.getElem_fin, Vector.getElem_ofFn, initialSlot]
  refine ⟨half (lanes (initialSlot lane)) false, half (lanes (initialSlot lane)) true,
    ?_, ?_, ?_, ?_⟩
  · rw [← low_lane_cell]
    exact observed.2 false
  · rw [← high_lane_cell]
    exact observed.2 true
  · rw [value]
    have bound := observed.1
    simp only [half, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    have upper : lanes (initialSlot lane) / 2 ^ 32 < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt upper]
    omega
  · rw [value]
    exact observed.1

/-- RV twin of `permutation_of_executions`; also exposes the per-state snapshots for the delegate link. -/
theorem rv_permutation_of_executions (states : Fin 362 → RV.State) (pointer : BitVec 32)
    (exec : ∀ index : Fin 361, RVExecutesAt index (states index.castSucc) (states index.succ))
    (pointerRead : (Cell.register 11).readRV (states 0) = some pointer)
    (initialReads : ∀ (slot : Fin 30) (high : Bool), ∃ value : BitVec 32,
      (laneCell pointer ⟨slot.val, by omega⟩ high).readRV (states 0) = some value) :
    ∃ input output : Vector Nat 25,
      Keccak.Permutation.RVWordMapping (states 0) (states 361) pointer input output ∧
      output = keccakPermutation input := by
  obtain ⟨_, lanes, _, snapshots, steps⟩ :=
    rv_chain_of_executions states pointer exec pointerRead initialReads
  refine ⟨logicalLanes 0 (lanes 0), logicalLanes 0 (lanes 361),
    ⟨pointerRead, rv_lanes_at_of_snapshot (snapshots 0), rv_lanes_at_of_snapshot (snapshots 361)⟩, ?_⟩
  exact permutation_of_physical_chain lanes fun index => steps index

end Airbender.Keccak.Split.Call.Proofs

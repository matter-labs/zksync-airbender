import Slop.KeccakSplit.Reference.SnapshotStep

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- The physical lanes after `count` calls, starting from `initial`. -/
def chainLanes (initial : LaneState) : Nat → LaneState
  | 0 => initial
  | count + 1 => microStep (Fin.ofNat 361 count) (chainLanes initial count)

/-- The x11 pointer read before call `index` is the pointer of every call. -/
theorem executes_pointer {index : Fin 361} {before after : State} {pointer : BitVec 32}
    (execution : ExecutesAt index before after)
    (read : (Cell.register 11).read before = .ok pointer before) :
    pointer.toNat % 256 = 0 ∧ (Cell.register 11).read after = .ok pointer after := by
  obtain ⟨called, input, arguments, calledRead, _, atomic⟩ := execution
  obtain ⟨_, argument, _, argumentRead, _, aligned⟩ := arguments
  have same := (EStateM.Result.ok.inj (calledRead.symm.trans read)).1
  have sameArgument := (EStateM.Result.ok.inj (argumentRead.symm.trans read)).1
  subst same
  subst sameArgument
  refine ⟨aligned, ?_⟩
  exact atomic_writes_reads atomic (writes_aligned index _ aligned _)
    (writes_distinct index _ aligned _) (by simp [writes]) (by decide)

/-- One executed call carries the x11 pointer and the physical snapshot forward. -/
theorem executes_snapshot {index : Fin 361} {before after : State} {pointer : BitVec 32}
    {lanes : LaneState} (execution : ExecutesAt index before after)
    (read : (Cell.register 11).read before = .ok pointer before)
    (snapshot : PhysicalSnapshot before pointer lanes) :
    PhysicalSnapshot after pointer (microStep index lanes) := by
  have aligned := (executes_pointer execution read).1
  obtain ⟨called, input, _, calledRead, reads, atomic⟩ := execution
  have same := (EStateM.Result.ok.inj (calledRead.symm.trans read)).1
  subst same
  exact snapshot_step index called aligned snapshot input reads atomic

/-- Two 32-bit words combine into the 64-bit lane whose halves they are. -/
theorem half_combine (low high : BitVec 32) (upper : Bool) :
    half (low.toNat + 2 ^ 32 * high.toNat) upper = if upper then high else low := by
  have lowBound := low.isLt
  have highBound := high.isLt
  apply BitVec.eq_of_toNat_eq
  cases upper
  · simp only [half, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  · simp only [half, ↓reduceIte, BitVec.toNat_ofNat]
    have quotient : (low.toNat + 2 ^ 32 * high.toNat) / 2 ^ 32 = high.toNat := by omega
    rw [quotient]
    omega

/-- Initial reads of the thirty physical lanes give an initial physical snapshot. -/
theorem initial_snapshot {state : State} {pointer : BitVec 32}
    (reads : ∀ (slot : Fin 30) (high : Bool), ∃ value : BitVec 32,
      (laneCell pointer ⟨slot.val, by omega⟩ high).read state = .ok value state) :
    ∃ lanes : LaneState, PhysicalSnapshot state pointer lanes := by
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

/-- The 361 executed calls share the x11 pointer, and their physical lane
snapshots evolve by `microStep`, call by call. -/
theorem chain_of_executions (states : Fin 362 → State) (pointer : BitVec 32)
    (exec : ∀ index : Fin 361, ExecutesAt index (states index.castSucc) (states index.succ))
    (pointerRead : (Cell.register 11).read (states 0) = .ok pointer (states 0))
    (initialReads : ∀ (slot : Fin 30) (high : Bool), ∃ value : BitVec 32,
      (laneCell pointer ⟨slot.val, by omega⟩ high).read (states 0) = .ok value (states 0)) :
    pointer.toNat % 256 = 0 ∧ ∃ lanes : Fin 362 → LaneState,
      (∀ index : Fin 362, (Cell.register 11).read (states index) = .ok pointer (states index)) ∧
      (∀ index : Fin 362, PhysicalSnapshot (states index) pointer (lanes index)) ∧
      (∀ index : Fin 361, lanes index.succ = microStep index (lanes index.castSucc)) := by
  obtain ⟨initial, initialSnapshot⟩ := initial_snapshot initialReads
  have carried (count : Nat) (bound : count < 362) :
      (Cell.register 11).read (states ⟨count, bound⟩) = .ok pointer (states ⟨count, bound⟩) ∧
      PhysicalSnapshot (states ⟨count, bound⟩) pointer (chainLanes initial count) := by
    induction count with
    | zero => exact ⟨pointerRead, initialSnapshot⟩
    | succ count ih =>
      obtain ⟨read, snapshot⟩ := ih (by omega)
      have execution := exec ⟨count, by omega⟩
      have call : Fin.ofNat 361 count = (⟨count, by omega⟩ : Fin 361) :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      exact ⟨(executes_pointer execution read).2, by
        rw [chainLanes, call]
        exact executes_snapshot execution read snapshot⟩
  refine ⟨(executes_pointer (exec 0) pointerRead).1, fun index => chainLanes initial index.val,
    fun index => (carried index.val index.isLt).1, fun index => (carried index.val index.isLt).2, ?_⟩
  intro index
  have call : Fin.ofNat 361 index.val = index := Fin.ext (Nat.mod_eq_of_lt index.isLt)
  simp only [Fin.val_succ, Fin.val_castSucc, chainLanes, call]

end Airbender.Keccak.Split.Call.Proofs

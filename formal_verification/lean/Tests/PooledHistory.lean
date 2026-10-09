import Airbender.Proofs.Trace.Pooled
import Tests.SubwordMemoryTimestamp

namespace Tests.PooledHistory
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

-- LBU x2,0(x1), then ADD x1,x2,x0. The corrupted ADD computes a consistent
-- local result from 19, but the preceding LBU wrote 18 to x2.
private def assignment (corrupt : Bool) : Nat → ZMod babyBearModulus
  | 0 | 35 => 4
  | 2 | 19 => 8
  | 21 => 12
  | 5 => 2
  | 23 => 6
  | 25 | 33 => if corrupt then 19 else 18
  | 31 | 4 | 7 | 10 | 42 | 43 | 44 => 1
  | 32 => 64
  | _ => 0

private def load : Row babyBearModulus PooledFamily :=
  ⟨.subwordMemory, Tests.SubwordMemoryTimestamp.assignment false⟩
private def add (corrupt : Bool) : Row babyBearModulus PooledFamily :=
  ⟨.addSub, assignment corrupt⟩
private def token (cell : Cell) (time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨cell.addressCode, (time, 0), Nat.pair lo hi⟩
private def trace (corrupt : Bool) : PooledTrace babyBearModulus where
  rows := [add corrupt, load]
  rom := ⟨ROM.table [] [], Verification.subwordTable (fun _ => 0)⟩
  initial := load.start
  terminal := (add corrupt).finish
  initialMemory := [token (.register 0) 0 0 0, token (.register 1) 0 1 64,
    token (.ram 4194304) 0 4660 22136, token (.register 2) 0 0 0]
  terminalMemory := [token (.register 0) 9 0 0, token (.register 1) 10 (if corrupt then 19 else 18) 0,
    token (.ram 4194304) 5 4660 22136, token (.register 2) 8 (if corrupt then 19 else 18) 0]

theorem local_add (corrupt : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment corrupt)) AddSub.clockConstraints := by
  cases corrupt <;>
    simp [AddSub.clockConstraints, AddSub.importedConstraints,
      AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus])
    | norm_num [babyBearModulus]

theorem accepted : Accepted (trace false) := by
  constructor
  · intro row member
    simp [trace] at member
    rcases member with rfl | rfl
    · exact local_add false
    · exact Tests.SubwordMemoryTimestamp.constraints false
  · intro row member
    simp [trace] at member
    rcases member with rfl | rfl <;> rfl
  · have linked : load.finish = (add false).start := rfl
    change [load.start, (add false).finish, load.finish].Perm
      [(add false).finish, (add false).start, load.start]
    rw [linked]
    exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
  · dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns, add, load, token,
      AddSub.importedConstraintsMemoryPorts, SubwordMemory.importedConstraintsMemoryPorts,
      AddSub.importedConstraintsTraceColumns, SubwordMemory.importedConstraintsTraceColumns]
    decide

private theorem boundary : ClockBoundary (trace false) := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro token member
    simp [trace] at member
    rcases member with rfl | rfl | rfl | rfl <;> constructor <;> decide

/-- The two families receive their per-row clock obligations from one global
    native permutation, not from separately supplied row assumptions. -/
theorem derived_clocks : ∀ row ∈ (trace false).rows,
    ClockEffects row.columns row.assignment :=
  Proofs.trace_clocks (by decide) (by decide) accepted boundary

/-- The same generic latest-write proof spans the LBU-to-ADD dependency. -/
theorem latest_reads : ∀ row ∈ (trace false).rows, ∀ port ∈ row.ports,
    LatestRead (trace false) row port :=
  Proofs.latest_reads (by decide) (by decide) accepted boundary (by decide)

/-- Global matching rejects the fabricated cross-family read, although both
    rows separately satisfy their actual imported constraints and setups. -/
theorem fabricated_read_rejected : ¬ Accepted (trace true) := by
  intro accepted
  have matching := accepted.memory
  have present : token (.register 2) 6 18 0 ∈
      (trace true).initialMemory ++ (trace true).rows.flatMap Row.writes := by decide
  have absent : token (.register 2) 6 18 0 ∉
      (trace true).terminalMemory ++ (trace true).rows.flatMap Row.reads := by decide
  exact absent (matching.mem_iff.mp present)

end Tests.PooledHistory

module
public import Slop.Trace.ROMView
public import Human.Helpers.Decoder.PooledExternalInput
public import Human.Circuits.WordMemory.Output
public import Human.Circuits.SubwordMemory.Output
public import Slop.JumpBranchSlt.Trace
public import Tests.JumpTimestamp

@[expose] public section

namespace Tests.JumpHistory
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

-- JAL x1,-4; the two x0 reads alias. The second must refer to the first
-- port's fresh timestamp. The old destination value is independently supplied.
def assignment (old : Nat) (rollover : Bool) (i : Nat) : ZMod babyBearModulus :=
  if i = 24 then (if rollover then 524284 else 4)
  else if i = 28 then old
  else JumpTimestamp.assignment rollover i

def row (old : Nat) (rollover : Bool) : Row babyBearModulus JumpBranchSlt.TraceKind :=
  ⟨.jumpBranchSlt, assignment old rollover⟩

def token (index low high value : Nat) : MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair index 0), (low, high), Nat.pair value 0⟩

def trace (old : Nat) (rollover : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.NativeTrace babyBearModulus where
  rows := [row old rollover]
  rom := rom
  initial := (row old rollover).start
  terminal := (row old rollover).finish
  initialMemory := [token 0 0 (if rollover then 7 else 0) 0,
    token 1 0 (if rollover then 7 else 0) 5]
  terminalMemory := [token 0 (if rollover then 524285 else 5) (if rollover then 7 else 0) 0,
    token 1 (if rollover then 524286 else 6) (if rollover then 7 else 0) 4]

theorem boundary (old : Nat) (rollover : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : ClockBoundary (trace old rollover rom) := by
  constructor
  · cases rollover <;>
      dsimp [trace, Row.start, Row.columns, row, rawPair, timeOfPair, decodeTimestamp,
        assignment, JumpTimestamp.assignment, JumpBranchSlt.importedConstraintsTraceColumns]
    all_goals constructor <;> decide
  · cases rollover <;>
      dsimp [trace, Row.start, Row.columns, row, rawPair, timeOfPair, Timestamp.value,
        assignment, JumpTimestamp.assignment, JumpBranchSlt.importedConstraintsTraceColumns]
    all_goals decide
  · intro actual member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> cases rollover <;> constructor <;> decide

private theorem unique (old : Nat) (rollover : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ((trace old rollover rom).initialMemory.map MemoryToken.address).Nodup := by
  change ([Nat.pair 0 (Nat.pair 0 0), Nat.pair 0 (Nat.pair 1 0)] : List Nat).Nodup
  decide

/-- The local circuit allows another unused old-rd value. Native matching
    rejects it against the fixed public seed; it cannot be chosen as a read. -/
theorem invented_old_destination_rejected (rollover : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : ¬ Accepted (trace 0 rollover rom) := by
  intro valid
  let prior := readToken (assignment 0 rollover) JumpBranchSlt.importedConstraintsMemoryPorts[2]
  have present : prior ∈ (trace 0 rollover rom).terminalMemory ++
      (trace 0 rollover rom).rows.flatMap Row.reads := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨row 0 rollover, by simp [trace], ?_⟩
    exact List.mem_map.mpr ⟨JumpBranchSlt.importedConstraintsMemoryPorts[2], by simp [row, Row.ports,
      JumpBranchSlt.importedConstraintsMemoryPorts], rfl⟩
  have matched := valid.memory.mem_iff.mpr present
  have absent : prior ∉ (trace 0 rollover rom).initialMemory ++
      (trace 0 rollover rom).rows.flatMap Row.writes := by
    cases rollover <;> dsimp [prior, trace, Row.writes, Row.ports, Row.columns, row,
      JumpBranchSlt.importedConstraintsMemoryPorts, JumpBranchSlt.importedConstraintsTraceColumns]
    all_goals decide
  exact absent matched

end Tests.JumpHistory

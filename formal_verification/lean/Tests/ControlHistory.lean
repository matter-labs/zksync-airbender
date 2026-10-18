import Airbender.Review.Trace.Families.JumpBranchSlt.History
import Tests.JumpDecoder

namespace Tests.ControlHistory
open Airbender Trace Verification
open Reference.Sail _root_.Sail.ArchSem

/-- Two x0 reads alias: the second must consume the first readonly clock refresh.
    The actual JAL link replaces the public old x1 value 123 with four. -/
def assignment (stale : Bool) (i : Nat) : ZMod mersenne31Modulus :=
  if i = 40 then 123 else if i = 54 then if stale then 0 else 4
  else Tests.JumpDecoder.assignment i

def nativeRow (stale : Bool) : Row mersenne31Modulus JumpBranchSltFamily :=
  ⟨.jumpBranchSlt, assignment stale⟩

private def cell (register time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair register 0), (time, 0), Nat.pair value 0⟩

def trace (stale : Bool) : Data mersenne31Modulus JumpBranchSltFamily where
  rows := [nativeRow stale]
  rom := ()
  initial := ⟨(0, 0), (4, 0)⟩
  terminal := ⟨(65532, 65535), (8, 0)⟩
  initialMemory := [cell 0 0 0, cell 1 0 123]
  terminalMemory := [cell 0 5 0, cell 1 6 4]

/-- Every native equation and query accepts both local alias timestamp choices. -/
theorem native_constraints (stale : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment stale))
      JumpBranchSlt.importedConstraints := by
  cases stale <;>
    simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
      environment, assignment, Tests.JumpDecoder.assignment, Tests.JumpPC.negativeJal,
      Tests.JumpControl.assignment]
  all_goals
    repeat' apply And.intro
    all_goals first | (apply range16_contains; decide) |
      (apply timestamp19_contains; decide) | try decide
    all_goals
      simp only [Lookup.Contains, fixed3, Table.toRaw, conditionalControlTable,
        jumpCleanupTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
        Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
        assignment, Tests.JumpDecoder.assignment, Tests.JumpPC.negativeJal,
        Tests.JumpControl.assignment]
      solve
      | refine ⟨⟨7, by decide⟩, ?_⟩
        norm_num [conditionalControlRow, controlFlag]
      | refine ⟨⟨65532, by decide⟩, ?_⟩
        norm_num [jumpCleanupRow]

theorem accepted : Accepted (trace false) := by
  constructor
  · intro actual member
    have same : actual = nativeRow false := by simpa [trace] using member
    subst actual
    exact native_constraints false
  · intro actual member
    have same : actual = nativeRow false := by simpa [trace] using member
    subst actual
    decide
  · change [(trace false).initial, (nativeRow false).finish].Perm
      [(trace false).terminal, (nativeRow false).start]
    have start : (nativeRow false).start = (trace false).initial := rfl
    have finish : (nativeRow false).finish = (trace false).terminal := rfl
    rw [start, finish]
    exact List.Perm.swap _ _ []
  · change ([cell 0 0 0, cell 1 0 123, cell 0 4 0, cell 0 5 0, cell 1 6 4]).Perm
      [cell 0 5 0, cell 1 6 4, cell 0 0 0, cell 0 4 0, cell 1 0 123]
    decide +kernel

def before : Reference.RiscV.Sail.State :=
  { JumpBranchSlt.NativeSetup.before with regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (123 : BitVec 32) |>.insert .PC (0 : BitVec 32)) }

theorem public_inputs : ImageBoundary (trace false) before [.register 0, .register 1] := by
  have zero : (Cell.register 0).read before = .ok (0 : BitVec 32) before := rfl
  have old : (Cell.register 1).read before = .ok (123 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (0 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · decide
  · simp only [initialImage, List.mapM_cons, List.mapM_nil, zero, old]
    rfl
  · rw [initialState, pc]
    rfl

/-- Actual Sail seed reads and accepted native matching construct complete Clean
    history; no expected read or per-row clock premise is supplied. -/
theorem public_history : ∃ history, MemoryHistory (trace false) history :=
  (JumpBranchSlt.public_memory_soundness public_inputs accepted).1

theorem second_latest : LatestRead (trace false) (nativeRow false)
    JumpBranchSlt.importedConstraintsMemoryPorts[1] :=
  (JumpBranchSlt.public_memory_soundness public_inputs accepted).2
    (nativeRow false) (by simp [trace]) _ (by
      change JumpBranchSlt.importedConstraintsMemoryPorts[1] ∈
        JumpBranchSlt.importedConstraintsMemoryPorts
      simp [JumpBranchSlt.importedConstraintsMemoryPorts])

/-- Native logical matching excludes the stale second x0 read. -/
theorem stale_rejected : ¬Accepted (trace true) := by
  intro h
  have count := h.memory.count_eq (cell 0 4 0)
  revert count
  decide +kernel

/-- Successful initialization supplies every local and prior port clock input. -/
theorem derived_clocks : ClockInputs (nativeRow false).columns (assignment false) :=
  Trace.Proofs.clock_inputs (by decide) accepted
    (Trace.Proofs.image_clock_boundary (by decide) public_inputs)
    (nativeRow false) (by simp [trace])

theorem advance :
    (decodeTimestamp (assignment false) JumpBranchSlt.importedConstraintsTraceColumns.finalTime).value =
      (decodeTimestamp (assignment false) JumpBranchSlt.importedConstraintsTraceColumns.initialTime).value + 4 :=
  JumpBranchSlt.Proofs.clock_advance (by decide) (native_constraints false) derived_clocks.initial

/-- The initialized memory proof also retains actual public decoder membership. -/
theorem exported_membership : ∃ i : Fin 1048576,
    JumpBranchSlt.decoderQuery (assignment false) = JumpBranchSlt.NativeSetup.controlDecoder.row i :=
  ⟨⟨0, by decide⟩, by decide +kernel⟩

theorem effects : ClockEffects (nativeRow false).columns (assignment false) :=
  Trace.Proofs.trace_clocks (by decide) accepted
    (Trace.Proofs.image_clock_boundary (by decide) public_inputs)
    (nativeRow false) (by simp [trace])

theorem terminal_clock :
    (timeOfPair (trace false).terminal.timestamp).value =
      (timeOfPair (trace false).initial.timestamp).value + 4 * (trace false).rows.length :=
  Trace.Proofs.trace_terminal_clock (by decide) accepted
    (Trace.Proofs.image_clock_boundary (by decide) public_inputs)

theorem missing_register_rejected :
    initialImage (p := mersenne31Modulus)
      { before with regs := Std.ExtDHashMap.emptyWithCapacity }
      [.register 0, .register 1] = none := by
  let missingState : Reference.RiscV.Sail.State :=
    { before with regs := Std.ExtDHashMap.emptyWithCapacity }
  change initialImage missingState [.register 0, .register 1] = none
  have zero : Cell.read (.register 0) missingState =
      .ok (0 : BitVec 32) missingState := rfl
  have absent : Cell.read (.register 1) missingState =
      .error _root_.Sail.Error.Unreachable missingState := by
    have missing : missingState.regs.get? .x1 = none := by
      simp [missingState]
    change run (SailRV32.readReg .x1) missingState = _
    dsimp [run, SailRV32.readReg, PreSail.readReg, interpretSailEffects, FreeM.liftM,
      interpretInstructionEffect]
    simp [missing, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.run]
  simp only [initialImage, List.mapM_cons, zero, absent]
  rfl

/-- Exercise the actual native 19-bit lower clock carry, retaining every query.
    This is a local row regression, separate from the initialized time-four trace. -/
def rollover (i : Nat) : ZMod mersenne31Modulus :=
  if i = 2 then 524284 else if i = 15 then 0 else if i = 16 ∨ i = 60 then 1
  else assignment false i

theorem rollover_constraints :
    FlatOperation.ConstraintsHoldFlat (environment rollover) JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, rollover, assignment, Tests.JumpDecoder.assignment, Tests.JumpPC.negativeJal,
    Tests.JumpControl.assignment]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, conditionalControlTable,
      jumpCleanupTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      rollover, assignment, Tests.JumpDecoder.assignment, Tests.JumpPC.negativeJal,
      Tests.JumpControl.assignment]
    solve
    | refine ⟨⟨7, by decide⟩, ?_⟩
      norm_num [conditionalControlRow, controlFlag]
    | refine ⟨⟨65532, by decide⟩, ?_⟩
      norm_num [jumpCleanupRow]

theorem rollover_advance :
    (decodeTimestamp rollover JumpBranchSlt.importedConstraintsTraceColumns.finalTime).lo = 0 ∧
    (decodeTimestamp rollover JumpBranchSlt.importedConstraintsTraceColumns.finalTime).hi = 1 ∧
    (decodeTimestamp rollover JumpBranchSlt.importedConstraintsTraceColumns.finalTime).value =
      (decodeTimestamp rollover JumpBranchSlt.importedConstraintsTraceColumns.initialTime).value + 4 :=
  ⟨by decide, by decide,
    JumpBranchSlt.Proofs.clock_advance (by decide) rollover_constraints (by constructor <;> decide)⟩

end Tests.ControlHistory

import Tests.AddSub
import Airbender.Review.Trace.Initialization

namespace Tests.InitializedHistory
open Airbender Trace
open Reference.Sail _root_.Sail.ArchSem

-- x1 + x1 -> x1. Readonly ports refresh the same cell at clocks 4 and 5;
-- the actual destination write at clock 6 replaces 123 with 246.
private def assignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 35 then 123 else if i = 47 then 4 else if i = 50 then 5
  else Tests.AddSub.row 1 123 123 0 246 0 0 0 0 0 4 0 0 0 i

private def nativeRow : Row mersenne31Modulus := ⟨.addSub, assignment⟩

private def cell (time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair 1 0), (time, 0), Nat.pair value 0⟩

private def trace : Data mersenne31Modulus where
  rows := [nativeRow]
  rom := ()
  initial := ⟨(0, 0), (4, 0)⟩
  terminal := ⟨(4, 0), (8, 0)⟩
  initialMemory := [cell 0 123]
  terminalMemory := [cell 6 246]

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, assignment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

private theorem accepted : Accepted trace := by
  constructor
  · intro row member
    have same : row = nativeRow := by simpa [trace] using member
    subst row
    exact satisfies
  · intro row member
    have same : row = nativeRow := by simpa [trace] using member
    subst row
    decide
  · change [trace.initial, nativeRow.finish].Perm [trace.terminal, nativeRow.start]
    have start : nativeRow.start = trace.initial := rfl
    have finish : nativeRow.finish = trace.terminal := rfl
    rw [start, finish]
    exact List.Perm.swap _ _ []
  · change ([cell 0 123, cell 4 123, cell 5 123, cell 6 246]).Perm
      [cell 6 246, cell 0 123, cell 4 123, cell 5 123]
    decide

private theorem boundary : ClockBoundary trace := by
  constructor
  · constructor <;> decide
  · decide
  · intro token member
    have same : token = cell 0 123 := by simpa [trace] using member
    subst token
    constructor <;> decide

private theorem unique : (trace.initialMemory.map MemoryToken.address).Nodup := by decide

/-- Nonempty application of the public trace theorem with aliased ports. -/
theorem complete_history : ∃ history, MemoryHistory trace history :=
  (native_memory_soundness accepted boundary unique).1

/-- Destination's old value comes from the second readonly refresh, not the seed. -/
theorem destination_latest : LatestRead trace nativeRow
    Airbender.AddSub.importedConstraintsMemoryPorts[2] :=
  (native_memory_soundness accepted boundary unique).2 nativeRow (by simp [trace]) _ (by
    change Airbender.AddSub.importedConstraintsMemoryPorts[2] ∈
      Airbender.AddSub.importedConstraintsMemoryPorts
    simp [Airbender.AddSub.importedConstraintsMemoryPorts])

private def staleAssignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 47 then 0 else assignment i

private def staleRow : Row mersenne31Modulus := ⟨.addSub, staleAssignment⟩
private def staleTrace : Data mersenne31Modulus := { trace with rows := [staleRow] }

/-- Local native constraints alone allow reusing the seed for the second read. -/
theorem stale_local_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment staleAssignment)
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, staleAssignment, assignment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

/-- Actual logical memory matching rejects that stale alias read. -/
theorem stale_history_rejected : ¬ Accepted staleTrace := by
  intro h
  have count := h.memory.count_eq (cell 4 123)
  revert count
  decide

private def before : Reference.RiscV.Sail.State where
  regs := (Std.ExtDHashMap.emptyWithCapacity)
    |>.insert .x1 (123 : BitVec 32) |>.insert .PC (0 : BitVec 32)
  mem := Std.ExtHashMap.emptyWithCapacity
  tags := ()
  cycleCount := 0
  sailOutput := #[]

private theorem public_inputs : ImageBoundary trace before [Cell.register 1] := by
  have read : (Cell.register 1).read before = .ok (123 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (0 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · decide
  · simp only [initialImage, List.mapM_cons, List.mapM_nil]
    rw [read]
    rfl
  · rw [initialState, pc]
    rfl

/-- The seed is now constructed from the original Sail read of public x1. -/
theorem public_image_history : ∃ history, MemoryHistory trace history :=
  (public_image_memory_soundness public_inputs accepted).1

-- Failure proofs follow the pinned source Tests/TraceInitialImage.lean.
/-- Missing public registers reject image construction rather than defaulting to zero. -/
theorem missing_register_rejected :
    initialImage (p := mersenne31Modulus) before [Cell.register 2] = none := by
  have absent : Cell.read (.register 2) before =
      .error _root_.Sail.Error.Unreachable before := by
    have missing : before.regs.get? .x2 = none := by
      simp [before, Std.ExtDHashMap.get?_insert]
    change run (SailRV32.readReg .x2) before = _
    dsimp [run, SailRV32.readReg, PreSail.readReg, interpretSailEffects, FreeM.liftM,
      interpretInstructionEffect]
    simp [missing, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.run]
  simp only [initialImage, List.mapM_cons, absent]
  rfl

/-- Missing byte memory also rejects the public image constructor. -/
theorem missing_bytes_rejected :
    initialImage (p := mersenne31Modulus) before [Cell.ram 0] = none := by
  have absent : Cell.read (.ram 0) before =
      .error (_root_.Sail.Error.OutOfMemoryRange 0) before := by
    simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, EStateM.bind, EStateM.get, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw, before]
  simp only [initialImage, List.mapM_cons, absent]
  rfl

end Tests.InitializedHistory

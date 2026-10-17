import Tests.AddSub
import Airbender.Review.Trace.SailHistory
import Airbender.Proofs.Trace.PortReads
import Airbender.Proofs.Trace.Arithmetic

namespace Tests.X0History
open Airbender Trace Reference.Sail

-- Original SUB x0,x1,x2 has raw result 2 from 5-3 and actual masked write zero.
private def assignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 6 then 2 else if i = 7 ∨ i = 37 then 0 else if i = 8 then 1
  else Tests.AddSub.row 4 5 3 0 2 0 0 0 0 0 4 0 0 0 i

private def nativeRow : Row mersenne31Modulus := ⟨.addSub, assignment⟩
private def cell (index time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair index 0), (time, 0), Nat.pair value 0⟩
private def trace : Data mersenne31Modulus where
  rows := [nativeRow]
  rom := ()
  initial := ⟨(0, 0), (4, 0)⟩
  terminal := ⟨(4, 0), (8, 0)⟩
  initialMemory := [cell 1 0 5, cell 2 0 3, cell 0 0 0]
  terminalMemory := [cell 1 4 5, cell 2 5 3, cell 0 6 0]

private theorem accepted : Accepted trace := by
  constructor
  · intro row member
    have same : row = nativeRow := by simpa [trace] using member
    subst row
    change FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
      Airbender.AddSub.importedConstraints
    simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, assignment, Tests.AddSub.row]
    repeat' apply And.intro
    all_goals first | decide | (apply Verification.range16_contains; decide) |
      (apply Verification.timestamp19_contains; decide)
  · intro row member
    have same : row = nativeRow := by simpa [trace] using member
    subst row
    decide
  · change [trace.initial, nativeRow.finish].Perm [trace.terminal, nativeRow.start]
    have start : nativeRow.start = trace.initial := rfl
    have finish : nativeRow.finish = trace.terminal := rfl
    rw [start, finish]
    exact List.Perm.swap _ _ []
  · change [cell 1 0 5, cell 2 0 3, cell 0 0 0, cell 1 4 5, cell 2 5 3, cell 0 6 0].Perm
      [cell 1 4 5, cell 2 5 3, cell 0 6 0, cell 1 0 5, cell 2 0 3, cell 0 0 0]
    decide

private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (5 : BitVec 32) |>.insert .x2 (3 : BitVec 32)
      |>.insert .PC (0 : BitVec 32))
    mem := (Std.ExtHashMap.emptyWithCapacity
      |>.insert 0 (0x33 : BitVec 8) |>.insert 1 0x80 |>.insert 2 0x20 |>.insert 3 0x40) }
private def cells : List Cell := [.register 1, .register 2, .register 0]

private theorem inputs : ImageBoundary trace before cells := by
  have left : (Cell.register 1).read before = .ok (5 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have right : (Cell.register 2).read before = .ok (3 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok (0 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · decide
  · simp only [cells, initialImage, List.mapM_cons, List.mapM_nil, left, right]
    rfl
  · rw [initialState, pc]
    rfl

private def entry : ProgramEntry :=
  ⟨0, 0x40208033, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 0, .SUB),
    ⟨.addSub, 1, 2, 0, ⟨0, 0⟩, 4, 0⟩⟩
private def setup : DecoderSetup := ⟨[entry], 1⟩
private theorem decoded : Decoded trace setup := by
  intro row member
  have same : row = nativeRow := by simpa [trace] using member
  subst row
  change ∃ i : Fin 2, nativeRow.decoderQuery = setup.row i
  exact ⟨⟨0, by decide⟩, by decide⟩
private theorem aligned : ∀ cell ∈ cells, cell.Aligned := by
  intro cell member
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> trivial

/-- Nonzero raw SUB operands/result do not require a v3 NOP projection. -/
theorem raw_result_retained : assignment 12 = 4 ∧ assignment 25 = 5 ∧
    assignment 27 = 3 ∧ assignment 29 = 2 ∧ assignment 37 = 0 := by decide

theorem initialized_zero_reads : ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
    port.address.code row.assignment = (Cell.register 0).addressCode →
      (readToken row.assignment port).value = 0 :=
  Trace.Proofs.zero_reads_of_preserving (by decide) accepted
    (Trace.Proofs.image_clock_boundary (by decide) inputs) inputs.image
    (Trace.Proofs.decoded_zero_preserving (by decide) accepted decoded)

/-- Grouping derives the states, and native masked x0 writes are actual Sail stutters. -/
theorem discarded_write_stutters :
    SailHistory cells (rowEvents trace.memoryEpoch nativeRow).reverse before before := by
  obtain ⟨_, rows, after, _, permutation, _, history, _⟩ :=
    Trace.Proofs.decoded_row_history (by decide) accepted
      (Trace.Proofs.image_clock_boundary (by decide) inputs) inputs.image inputs.domain aligned decoded
  have same : rows = [nativeRow] := List.perm_singleton.mp permutation
  subst rows
  have single : SailHistory cells (rowEvents trace.memoryEpoch nativeRow).reverse before after := by
    simpa using history
  have written := Trace.Proofs.row_history_write trace.memoryEpoch single
    (port := Airbender.AddSub.importedConstraintsMemoryPorts[2]) (by rfl)
    (cell := Cell.register 0) (by rfl)
  change EStateM.Result.ok () before = .ok () after at written
  have same := (EStateM.Result.ok.inj written).2
  rw [← same] at single
  exact single

set_option maxRecDepth 32768 in
/-- The retained SUB opcode is built from actual public little-endian bytes. -/
theorem setup_built : decoderSetupImage before 1 1 = some setup := by
  have bytes : (Cell.ram 0).read before = .ok 0x40208033 before := by
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]
  have program : programImage before [0] = some [entry] := by
    simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, bind, Option.bind]
    rfl
  change (programImage before [0]).bind (fun entries => some ⟨entries, 1⟩) = some setup
  rw [program]
  rfl

/-- Original SUB-to-x0 retires PC+4 while its actual native data write stutters.
    No local decoder/operand/Sail-read interface is supplied by this regression. -/
theorem discarded_sail_retirement :
    run (Reference.RiscV.Sail.normalStep
      (SailRV32.Functions.execute_RTYPE (.Regidx 2) (.Regidx 1) (.Regidx 0) .SUB)) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState before 4) := by
  have checked := Trace.Proofs.arithmetic_row_execution (w := assignment) (before := before)
    (by decide) inputs setup_built accepted decoded
    (by simp [trace, nativeRow]) (entry := entry) rfl (by decide) .sub 1 2 0 0 0 rfl discarded_write_stutters
    (Trace.Proofs.initial_state_pc (by decide) inputs.initial)
  exact checked

end Tests.X0History

import Tests.AddSub
import Airbender.Review.Trace.Families.AddSub.Theorems

namespace Tests.ArithmeticExecution
open Airbender Trace Reference.Sail _root_.Sail.ArchSem

-- ADD x1,x1,x1 followed by ADDI x2,x1,1. The witness list deliberately stores
-- the rows backwards; accepted clocks/history must recover order and the 246 read.
private def first (i : Nat) : ZMod mersenne31Modulus :=
  if i = 35 then 123 else if i = 47 then 4 else if i = 50 then 5
  else Tests.AddSub.row 1 123 123 0 246 0 0 0 0 0 4 0 0 0 i
private def second (i : Nat) : ZMod mersenne31Modulus :=
  if i = 2 then 8 else if i = 15 then 12 else if i = 6 then 0 else if i = 7 then 2
  else if i = 39 then 1801116374 else if i = 44 then 6
  else Tests.AddSub.row 2 246 0 1 247 0 0 0 4 0 8 0 0 0 i
private def firstRow : Row mersenne31Modulus := ⟨.addSub, first⟩
private def secondRow : Row mersenne31Modulus := ⟨.addSub, second⟩
private def token (index time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair index 0), (time, 0), Nat.pair value 0⟩
private def trace : Data mersenne31Modulus where
  rows := [secondRow, firstRow]
  rom := ()
  initial := ⟨(0, 0), (4, 0)⟩
  terminal := ⟨(8, 0), (12, 0)⟩
  initialMemory := [token 1 0 123, token 0 0 0, token 2 0 0]
  terminalMemory := [token 1 8 246, token 0 9 0, token 2 10 247]

private theorem first_satisfies : FlatOperation.ConstraintsHoldFlat (Verification.environment first)
    Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, first, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)
private theorem second_satisfies : FlatOperation.ConstraintsHoldFlat (Verification.environment second)
    Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, second, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

private theorem accepted : Accepted trace := by
  constructor
  · intro row member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact second_satisfies
    · exact first_satisfies
  · intro row member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · change [trace.initial, trace.terminal, secondRow.start].Perm
      [trace.terminal, secondRow.start, trace.initial]
    exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
  · change [token 1 0 123, token 0 0 0, token 2 0 0,
        token 1 8 246, token 0 9 0, token 2 10 247,
        token 1 4 123, token 1 5 123, token 1 6 246].Perm
      [token 1 8 246, token 0 9 0, token 2 10 247,
        token 1 6 246, token 0 0 0, token 2 0 0,
        token 1 0 123, token 1 4 123, token 1 5 123]
    decide

private def before : Reference.RiscV.Sail.State where
  regs := (Std.ExtDHashMap.emptyWithCapacity
    |>.insert .x1 (123 : BitVec 32) |>.insert .x2 (0 : BitVec 32) |>.insert .PC (0 : BitVec 32))
  mem := (Std.ExtHashMap.emptyWithCapacity
    |>.insert 0 (0xb3 : BitVec 8) |>.insert 1 0x80 |>.insert 2 0x10 |>.insert 3 0
    |>.insert 4 0x13 |>.insert 5 0x81 |>.insert 6 0x10 |>.insert 7 0)
  tags := ()
  cycleCount := 0
  sailOutput := #[]
private def cells : List Cell := [.register 1, .register 0, .register 2]
private theorem inputs : ImageBoundary trace before cells := by
  have left : (Cell.register 1).read before = .ok (123 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have right : (Cell.register 2).read before = .ok (0 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok (0 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · decide
  · simp only [cells, initialImage, List.mapM_cons, List.mapM_nil, left, right]
    rfl
  · rw [initialState, pc]; rfl
private def addEntry : ProgramEntry :=
  ⟨0, 0x001080b3, .RTYPE (.Regidx 1, .Regidx 1, .Regidx 1, .ADD),
    ⟨.addSub, 1, 1, 1, ⟨0, 0⟩, 1, 0⟩⟩
private def addiEntry : ProgramEntry :=
  ⟨4, 0x00108113, .ITYPE (1, .Regidx 1, .Regidx 2, .ADDI),
    ⟨.addSub, 1, 0, 2, ⟨1, 0⟩, 2, 0⟩⟩
private def setup : DecoderSetup := ⟨[addEntry, addiEntry], 0⟩

set_option maxRecDepth 32768 in
theorem setup_built : decoderSetupImage before 2 1 = some setup := by
  have bytes0 : (Cell.ram 0).read before = .ok 0x001080b3 before := by
    simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]
  have bytes4 : (Cell.ram 4).read before = .ok 0x00108113 before := by
    simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]
  have program : programImage before [0, 4] = some [addEntry, addiEntry] := by
    simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes0, bytes4, bind, Option.bind]
    rfl
  change (programImage before [0, 4]).bind (fun entries => some ⟨entries, 0⟩) = some setup
  rw [program]; rfl
private theorem decoded : Decoded trace setup := by
  intro row member
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · change ∃ i : Fin 2, secondRow.decoderQuery = setup.row i
    exact ⟨⟨1, by decide⟩, by decide⟩
  · change ∃ i : Fin 2, firstRow.decoderQuery = setup.row i
    exact ⟨⟨0, by decide⟩, by decide⟩
private theorem aligned : ∀ cell ∈ cells, cell.Aligned := by
  intro cell member
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> trivial

/-- Two dependent rows execute in clock order despite reversed witness order. -/
theorem sail_execution : Realizes (SailStep setup.program) trace before cells :=
  public_sail_execution inputs setup_built accepted decoded aligned

/-- The original fetched/decoded Sail trace reaches PC 8 and x2=247. Neither
    the 246 intermediate read nor the final register value is an input premise. -/
theorem dependent_final_values : ∃ after, SailTrace setup.program before after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok (8 : BitVec 32) after ∧
    run (SailRV32.Functions.rX_bits (.Regidx 2)) after = .ok (247 : BitVec 32) after := by
  obtain ⟨after, execution, pc, values⟩ := sail_execution
  obtain ⟨target, _, address, read⟩ := values (token 2 10 247) (by simp [trace])
  have same : target = Cell.register 2 := Trace.Proofs.cell_address_injective address
  subst target
  simp only [id_eq, MemoryToken.word, token, Nat.unpair_pair] at read
  exact ⟨after, execution, pc, read⟩

end Tests.ArithmeticExecution

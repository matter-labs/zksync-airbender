import Airbender.Proofs.Trace.ZeroRegister
import Airbender.Proofs.Trace.RowHistory
import Airbender.Proofs.Trace.PortReads
import Airbender.Proofs.Trace.Arithmetic
import Airbender.Proofs.BabyBear
import Airbender.Review.Trace.ROM

namespace Tests.TraceZeroRegister
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

-- Original ADD x0,x1,x2 becomes a native ADD with three x0 accesses.
-- Repeated reads use the preceding native refresh writes, at clocks 4 and 5.
def assignment : Nat → ZMod babyBearModulus
  | 2 | 19 | 27 => 4
  | 21 => 8
  | 35 => 5
  | 4 | 10 | 42 | 43 | 44 => 1
  | _ => 0
def row : Row babyBearModulus := ⟨.addSub, assignment⟩
private def token (time : Nat) : MemoryToken babyBearModulus := ⟨0, (time, 0), 0⟩
private def cells : List Cell := [.register 0, .register 1, .register 2]
private def sourceTokens : List (MemoryToken babyBearModulus) :=
  [(Cell.register 1).initialToken 5, (Cell.register 2).initialToken 7]
private def rom : Table (ZMod babyBearModulus) (fields 9) := ROM.table cells (token 0 :: sourceTokens)
private def trace : Data babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := token 0 :: sourceTokens
  terminalMemory := token 6 :: sourceTokens
private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x1 (5 : BitVec 32)
      |>.insert .x2 (7 : BitVec 32) |>.insert .PC 0
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 0 (0x33 : BitVec 8)
      |>.insert 1 0x80 |>.insert 2 0x20 |>.insert 3 0 }
private def entry : ProgramEntry :=
  ⟨0, 0x00208033, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 0, .ADD),
    ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩

theorem initial_image : initialImage before cells = some trace.initialMemory := by
  have one : (Cell.register 1).read before = .ok 5 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have two : (Cell.register 2).read before = .ok 7 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  change List.mapM _ [Cell.register 0, Cell.register 1, Cell.register 2] = _
  simp only [List.mapM_cons, List.mapM_nil, one, two, bind, Option.bind]
  rfl

theorem program_image : programImage before [0] = some [entry] := by
  have bytes : (Cell.ram 0).read before = .ok 0x00208033 before := by
    simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, Std.ExtHashMap.getElem_insert]
  have decoded : SailRV32.Functions.encdec_backwards 0x00208033 =
      (_root_.Sail.ArchSem.FreeM.pure (.RTYPE (.Regidx 2, .Regidx 1, .Regidx 0, .ADD)) : SailRV32.SailM _) := rfl
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith,
    bytes, decoded, bind, Option.bind]
  rfl

theorem decoder_bound : Decoded trace [entry] := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, row.decoderQuery = _
  exact ⟨0, by decide⟩

theorem local_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | norm_num [babyBearModulus]

theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact local_satisfies
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp only [trace]
    decide

private theorem boundary : ClockBoundary trace := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro source member
    simp only [trace, sourceTokens, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

theorem native_zero_reads : ∀ port ∈ row.ports,
    port.address.code assignment = (Cell.register 0).addressCode →
    (readToken assignment port).value = 0 :=
  Proofs.native_zero_reads Proofs.standardDecoderRules (by decide) (by decide) accepted boundary initial_image
    program_image decoder_bound row (List.mem_singleton_self row)

theorem native_zero_writes : ∀ event ∈ trace.nativeEvents,
    event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0 :=
  Proofs.native_zero_writes Proofs.standardDecoderRules (by decide) (by decide) accepted boundary initial_image
    program_image decoder_bound

theorem derived_sail_history : ∃ (history : TimestampSortedMemoryAccessList)
    (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    MemoryHistory trace history ∧ events.Perm trace.nativeEvents ∧
    SailHistory cells events before after ∧ SailStateMatches cells history after := by
  obtain ⟨history, events, _, after, consistent, _, permutation, execution, final⟩ :=
    Proofs.decoded_sail_history Proofs.standardDecoderRules (by decide) (by decide) accepted boundary initial_image
      (by decide) (by
        intro cell member
        simp only [cells, List.mem_cons, List.mem_nil_iff, or_false] at member
        rcases member with rfl | rfl | rfl <;> trivial)
      program_image decoder_bound
  exact ⟨history, events, after, consistent, permutation, execution, final⟩

theorem load_x0_preprocessing (immediate : BitVec 12) (rs1 : BitVec 5) :
    decoderFields (.LOAD (immediate, .Regidx rs1, .Regidx 0, false, 4)) =
      some ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ := rfl

private def mutated (index : Nat) : ZMod babyBearModulus :=
  if index = 33 then 1 else assignment index

theorem nonzero_native_output_rejected : ¬ FlatOperation.ConstraintsHoldFlat
    (Verification.environment mutated) AddSub.importedConstraints := by
  intro constraints
  have result := AddSub.Proofs.zero_operands_result (by decide) constraints rfl (by
    intro k lower upper
    interval_cases k <;> rfl) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  change (Word.mk 1 0).toBitVec = 0 at result
  contradiction

theorem grouped_native_stutter : ∃ rows : List (Row babyBearModulus),
    rows.Perm trace.rows ∧ SailHistory cells
      (rows.flatMap fun row => (Proofs.rowEvents trace.memoryEpoch row).reverse) before before := by
  obtain ⟨_, rows, after, _, permutation, _, execution, _⟩ :=
    Proofs.decoded_row_history Proofs.standardDecoderRules (by decide) (by decide) accepted boundary initial_image
      (by decide) (by
        intro cell member
        simp only [cells, List.mem_cons, List.mem_nil_iff, or_false] at member
        rcases member with rfl | rfl | rfl <;> trivial)
      program_image decoder_bound
  have only : rows = [row] := List.perm_singleton.mp permutation
  subst rows
  have three := execution
  simp only [List.flatMap_singleton] at three
  obtain ⟨_, _, destination, _, _, _, _, _, address, _, _, _, written⟩ :=
    Proofs.sail_history_row_reads three rfl rfl
  change destination.addressCode = (Cell.register 0).addressCode at address
  have same := Proofs.cell_address_injective address
  subst destination
  change Reference.Sail.run (SailRV32.Functions.wX_bits (.Regidx 0) 0) before = .ok () after at written
  have stutter : Reference.Sail.run (SailRV32.Functions.wX_bits (.Regidx 0) 0) before = .ok () before := rfl
  have same := (EStateM.Result.ok.inj (written.symm.trans stutter)).2
  subst after
  exact ⟨[row], permutation, execution⟩

set_option maxHeartbeats 2000000 in
theorem preprocessed_source_from_ports :
    Reference.Sail.run (SailRV32.Functions.rX_bits (.Regidx 0)) before = .ok 0 before := by
  obtain ⟨rows, permutation, history⟩ := grouped_native_stutter
  have only : rows = [row] := List.perm_singleton.mp permutation
  subst rows
  simp only [List.flatMap_singleton] at history
  exact Proofs.row_history_source_read (by decide) trace.memoryEpoch history
    (entry := entry) (by decide) (port := AddSub.importedConstraintsMemoryPorts[0]) rfl

set_option maxHeartbeats 2000000 in
theorem discarded_write_from_ports :
    Reference.Sail.run (SailRV32.Functions.wX_bits (.Regidx 0) 0) before = .ok () before := by
  obtain ⟨rows, permutation, history⟩ := grouped_native_stutter
  have only : rows = [row] := List.perm_singleton.mp permutation
  subst rows
  simp only [List.flatMap_singleton] at history
  exact Proofs.row_history_write (row := row) trace.memoryEpoch history
    (port := AddSub.importedConstraintsMemoryPorts[2]) rfl
    (cell := .register 0) rfl

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The original ADD still reads x1=5 and x2=7 when rd is x0. Its zeroed native
    operands are never substituted for those original Sail reads. -/
theorem actual_discarded_add_step :
    Reference.Sail.run (Reference.RiscV.Sail.normalStep
      (SailRV32.Functions.execute_RTYPE (.Regidx 2) (.Regidx 1) (.Regidx 0) .ADD)) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { before with regs := before.regs.insert .nextPC (4 : BitVec 32) |>.insert .PC 4 } := by
  obtain ⟨rows, permutation, history⟩ := grouped_native_stutter
  have only : rows = [row] := List.perm_singleton.mp permutation
  subst rows
  simp only [List.flatMap_singleton] at history
  exact Proofs.arithmetic_row_execution (by decide) (by decide)
    accepted boundary initial_image rfl (by
      change (Word.mk 0 0).Bounded
      constructor <;> decide)
    (w := assignment) (List.mem_singleton_self row) (entry := entry) rfl (by decide)
    .add 1 2 0 0 0 (by decide) rfl (SailHistory.nil before) history (by
      apply Reference.RiscV.Sail.read_register
      simp [assignment, before,
        Word.toBitVec, Word.value, limbBase])

end Tests.TraceZeroRegister

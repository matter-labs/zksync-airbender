import Airbender.Proofs.Trace.ZeroRegister
import Airbender.Proofs.Trace.RowHistory
import Airbender.Proofs.BabyBear
import Airbender.Review.Trace.ROM

namespace Tests.TraceZeroRegister
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

-- Original ADD x0,x1,x2 becomes a native ADD with three x0 accesses.
-- Repeated reads use the preceding native refresh writes, at clocks 4 and 5.
private def assignment : Nat → ZMod babyBearModulus
  | 2 | 19 | 27 => 4
  | 21 => 8
  | 35 => 5
  | 4 | 10 | 42 | 43 | 44 => 1
  | _ => 0
private def row : Row babyBearModulus := ⟨.addSub, assignment⟩
private def token (time : Nat) : MemoryToken babyBearModulus := ⟨0, (time, 0), 0⟩
private def cells : List Cell := [.register 0]
private def rom : Table (ZMod babyBearModulus) (fields 9) := ROM.table cells [token 0]
private def trace : Data babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := [token 0]
  terminalMemory := [token 6]
private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x1 (5 : BitVec 32)
      |>.insert .x2 (7 : BitVec 32) |>.insert .PC 0
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 0 (0x33 : BitVec 8)
      |>.insert 1 0x80 |>.insert 2 0x20 |>.insert 3 0 }
private def entry : ProgramEntry :=
  ⟨0, 0x00208033, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 0, .ADD),
    ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1⟩⟩

theorem initial_image : initialImage before cells = some trace.initialMemory := rfl

theorem program_image : programImage before [0] = some [entry] := by
  have bytes : (Cell.ram 0).read before = .ok 0x00208033 before := by
    simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, Std.ExtHashMap.getElem_insert]
  have decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards 0x00208033) before =
      .ok (.RTYPE (.Regidx 2, .Regidx 1, .Regidx 0, .ADD)) before := rfl
  simp only [Trace.programImage, List.mapM_cons, List.mapM_nil, programEntry,
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
    simp only [trace, List.mem_singleton] at member
    subst source
    constructor <;> decide

theorem native_zero_reads : ∀ port ∈ row.ports,
    port.address.code assignment = (Cell.register 0).addressCode →
    (readToken assignment port).value = 0 :=
  Proofs.native_zero_reads (by decide) (by decide) accepted boundary initial_image
    program_image decoder_bound row (List.mem_singleton_self row)

theorem native_zero_writes : ∀ event ∈ trace.nativeEvents,
    event.2.1 = (Cell.register 0).addressCode → Proofs.memoryWord event.2.2.2 = 0 :=
  Proofs.native_zero_writes (by decide) (by decide) accepted boundary initial_image
    program_image decoder_bound

theorem derived_sail_history : ∃ (history : TimestampSortedMemoryAccessList)
    (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    MemoryHistory trace history ∧ events.Perm trace.nativeEvents ∧
    Proofs.SailHistory cells events before after ∧ Proofs.SailStateMatches cells history after := by
  obtain ⟨history, events, _, after, consistent, _, permutation, execution, final⟩ :=
    Proofs.decoded_sail_history (by decide) (by decide) accepted boundary initial_image
      (by decide) (by intro cell member; simp [cells] at member; subst cell; trivial)
      program_image decoder_bound
  exact ⟨history, events, after, consistent, permutation, execution, final⟩

theorem load_x0_preprocessing (immediate : BitVec 12) (rs1 : BitVec 5) :
    decoderFields (.LOAD (immediate, .Regidx rs1, .Regidx 0, false, 4)) =
      some ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1⟩ := rfl

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
    rows.Perm trace.rows ∧ Proofs.SailHistory cells
      (rows.flatMap fun row => (Proofs.rowEvents trace.memoryEpoch row).reverse) before before := by
  obtain ⟨_, rows, after, _, permutation, _, execution, _⟩ :=
    Proofs.decoded_row_history (by decide) (by decide) accepted boundary initial_image
      (by decide) (by intro cell member; simp [cells] at member; subst cell; trivial)
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

end Tests.TraceZeroRegister

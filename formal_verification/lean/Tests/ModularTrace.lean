import Airbender.Review.Trace.Modular.Theorems
import Airbender.Review.Trace.Modular.ExternalTheorems
import Tests.TraceExecution

namespace Tests.ModularTrace
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open Trace.Proofs _root_.Sail.ArchSem
open Airbender.AddSub
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

-- Public ADDI inputs, all four dependent modular operations (with aliased old
-- destination), every discarded custom form, and an ordinary ADD consumer.
private def assignment (index : Fin 11) : Nat → ZMod babyBearModulus :=
  match index.val with
  | 0 => fun column => match column with
    | 2 => 4
    | 4 => 1
    | 7 => 1
    | 8 => 11
    | 10 => 1
    | 19 => 4
    | 21 => 8
    | 27 => 4
    | 33 => 11
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | _ => 0
  | 1 => fun column => match column with
    | 0 => 4
    | 2 => 8
    | 4 => 1
    | 7 => 2
    | 8 => 3
    | 10 => 1
    | 19 => 8
    | 21 => 12
    | 23 => 5
    | 27 => 8
    | 33 => 3
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | _ => 0
  | 2 => fun column => match column with
    | 0 => 8
    | 2 => 12
    | 4 => 1
    | 5 => 1
    | 6 => 2
    | 7 => 3
    | 13 => 1
    | 19 => 12
    | 21 => 16
    | 23 => 6
    | 25 => 11
    | 27 => 10
    | 29 => 3
    | 33 => 14
    | 37 => 13
    | 38 => 34816
    | 40 => 1
    | 41 => 943718385
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | _ => 0
  | 3 => fun column => match column with
    | 0 => 12
    | 2 => 16
    | 4 => 1
    | 5 => 3
    | 6 => 1
    | 7 => 3
    | 14 => 1
    | 19 => 16
    | 21 => 20
    | 23 => 14
    | 25 => 14
    | 27 => 12
    | 29 => 11
    | 31 => 14
    | 33 => 3
    | 35 => 16
    | 37 => 2
    | 38 => 34816
    | 40 => 1
    | 41 => 377487288
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | _ => 0
  | 4 => fun column => match column with
    | 0 => 16
    | 2 => 20
    | 4 => 1
    | 5 => 3
    | 6 => 2
    | 7 => 3
    | 15 => 1
    | 19 => 20
    | 21 => 24
    | 23 => 18
    | 25 => 3
    | 27 => 13
    | 29 => 3
    | 31 => 3
    | 33 => 65532
    | 34 => 6719
    | 35 => 20
    | 37 => 65531
    | 38 => 41535
    | 40 => 1
    | 41 => 440401916
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | _ => 0
  | 5 => fun column => match column with
    | 0 => 20
    | 2 => 24
    | 4 => 1
    | 5 => 3
    | 6 => 2
    | 7 => 3
    | 16 => 1
    | 19 => 24
    | 21 => 28
    | 23 => 22
    | 25 => 65532
    | 26 => 6719
    | 27 => 21
    | 29 => 3
    | 31 => 65532
    | 32 => 6719
    | 33 => 2
    | 34 => 8790
    | 35 => 24
    | 37 => 1
    | 38 => 43606
    | 40 => 1
    | 41 => 576061442
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | _ => 0
  | 6 => fun column => match column with
    | 0 => 24
    | 2 => 28
    | 4 => 1
    | 10 => 1
    | 19 => 28
    | 21 => 32
    | 23 => 9
    | 27 => 28
    | 35 => 29
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | _ => 0
  | 7 => fun column => match column with
    | 0 => 28
    | 2 => 32
    | 4 => 1
    | 10 => 1
    | 19 => 32
    | 21 => 36
    | 23 => 30
    | 27 => 32
    | 35 => 33
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | _ => 0
  | 8 => fun column => match column with
    | 0 => 32
    | 2 => 36
    | 4 => 1
    | 10 => 1
    | 19 => 36
    | 21 => 40
    | 23 => 34
    | 27 => 36
    | 35 => 37
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | _ => 0
  | 9 => fun column => match column with
    | 0 => 36
    | 2 => 40
    | 4 => 1
    | 10 => 1
    | 19 => 40
    | 21 => 44
    | 23 => 38
    | 27 => 40
    | 35 => 41
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | _ => 0
  | 10 => fun column => match column with
    | 0 => 40
    | 2 => 44
    | 4 => 1
    | 5 => 3
    | 7 => 4
    | 10 => 1
    | 19 => 44
    | 21 => 48
    | 23 => 26
    | 25 => 2
    | 26 => 8790
    | 27 => 42
    | 33 => 2
    | 34 => 8790
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | _ => 0
  | _ => fun _ => 0

private def row (index : Fin 11) : Row babyBearModulus PooledFamily := ⟨.addSub, assignment index⟩
private def token (index time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (time, 0), Nat.pair lo hi⟩
private def cells := Tests.TraceExecution.cells
private def seed : List (MemoryToken babyBearModulus) :=
  (List.range 32).map fun index => token index 0 0 0

private def program : List PooledProgramEntry := [
  ⟨0, 0x00b00093, SailRV32.instruction.ITYPE (11, .Regidx 0, .Regidx 1, .ADDI), ⟨.addSub, 0, 0, 1, ⟨11, 0⟩, 1, 0⟩⟩,
  ⟨4, 0x00300113, SailRV32.instruction.ITYPE (3, .Regidx 0, .Regidx 2, .ADDI), ⟨.addSub, 0, 0, 2, ⟨3, 0⟩, 1, 0⟩⟩,
  ⟨8, 0x8220c1f3, Modular.instruction .add 1 2 3, ⟨.addSub, 1, 2, 3, ⟨0, 0⟩, 8, 0⟩⟩,
  ⟨12, 0x8611c1f3, Modular.instruction .sub 3 1 3, ⟨.addSub, 3, 1, 3, ⟨0, 0⟩, 16, 0⟩⟩,
  ⟨16, 0x8a21c1f3, Modular.instruction .mul 3 2 3, ⟨.addSub, 3, 2, 3, ⟨0, 0⟩, 32, 0⟩⟩,
  ⟨20, 0x8e21c1f3, Modular.instruction .fma 3 2 3, ⟨.addSub, 3, 2, 3, ⟨0, 0⟩, 64, 0⟩⟩,
  ⟨24, 0x8220c073, Modular.instruction .add 1 2 0, ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩,
  ⟨28, 0x8620c073, Modular.instruction .sub 1 2 0, ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩,
  ⟨32, 0x8a20c073, Modular.instruction .mul 1 2 0, ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩,
  ⟨36, 0x8e20c073, Modular.instruction .fma 1 2 0, ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩,
  ⟨40, 0x00018233, SailRV32.instruction.RTYPE (.Regidx 0, .Regidx 3, .Regidx 4, .ADD), ⟨.addSub, 3, 0, 4, ⟨0, 0⟩, 1, 0⟩⟩]

private def before : State :=
  { Tests.TraceExecution.before with
    regs := Tests.TraceExecution.before.regs.insert .mseccfg 0 |>.insert .x1 0
    mem := Std.ExtHashMap.emptyWithCapacity
      |>.insert 0 (0x93 : BitVec 8)
      |>.insert 1 (0x00 : BitVec 8)
      |>.insert 2 (0xb0 : BitVec 8)
      |>.insert 3 (0x00 : BitVec 8)
      |>.insert 4 (0x13 : BitVec 8)
      |>.insert 5 (0x01 : BitVec 8)
      |>.insert 6 (0x30 : BitVec 8)
      |>.insert 7 (0x00 : BitVec 8)
      |>.insert 8 (0xf3 : BitVec 8)
      |>.insert 9 (0xc1 : BitVec 8)
      |>.insert 10 (0x20 : BitVec 8)
      |>.insert 11 (0x82 : BitVec 8)
      |>.insert 12 (0xf3 : BitVec 8)
      |>.insert 13 (0xc1 : BitVec 8)
      |>.insert 14 (0x11 : BitVec 8)
      |>.insert 15 (0x86 : BitVec 8)
      |>.insert 16 (0xf3 : BitVec 8)
      |>.insert 17 (0xc1 : BitVec 8)
      |>.insert 18 (0x21 : BitVec 8)
      |>.insert 19 (0x8a : BitVec 8)
      |>.insert 20 (0xf3 : BitVec 8)
      |>.insert 21 (0xc1 : BitVec 8)
      |>.insert 22 (0x21 : BitVec 8)
      |>.insert 23 (0x8e : BitVec 8)
      |>.insert 24 (0x73 : BitVec 8)
      |>.insert 25 (0xc0 : BitVec 8)
      |>.insert 26 (0x20 : BitVec 8)
      |>.insert 27 (0x82 : BitVec 8)
      |>.insert 28 (0x73 : BitVec 8)
      |>.insert 29 (0xc0 : BitVec 8)
      |>.insert 30 (0x20 : BitVec 8)
      |>.insert 31 (0x86 : BitVec 8)
      |>.insert 32 (0x73 : BitVec 8)
      |>.insert 33 (0xc0 : BitVec 8)
      |>.insert 34 (0x20 : BitVec 8)
      |>.insert 35 (0x8a : BitVec 8)
      |>.insert 36 (0x73 : BitVec 8)
      |>.insert 37 (0xc0 : BitVec 8)
      |>.insert 38 (0x20 : BitVec 8)
      |>.insert 39 (0x8e : BitVec 8)
      |>.insert 40 (0x33 : BitVec 8)
      |>.insert 41 (0x82 : BitVec 8)
      |>.insert 42 (0x01 : BitVec 8)
      |>.insert 43 (0x00 : BitVec 8)
  }

private def trace : PooledTrace babyBearModulus where
  rows := (List.finRange 11).reverse.map row
  rom := ⟨ROM.table cells seed, Verification.subwordTable (ROM.words before)⟩
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 44 (48, 0)
  initialMemory := seed
  terminalMemory := [
    token 0 45 0 0,
    token 1 17 11 0,
    token 2 25 3 0,
    token 3 44 2 8790,
    token 4 46 2 8790] ++ seed.drop 5

private theorem constraints (index : Fin 11) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment index)) AddSub.clockConstraints := by
  fin_cases index <;>
    simp [AddSub.clockConstraints, AddSub.importedConstraints,
      AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)
    | (apply Trace.Proofs.range_contains; decide)

private theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact constraints index
  · intro actual member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    fin_cases index <;> rfl
  · change ([trace.initial] ++ trace.rows.map Row.finish).Perm
      (trace.rows.map Row.finish ++ [trace.initial])
    exact List.perm_append_comm
  · decide

private theorem clocks : ClockBoundary trace := by
  constructor
  · constructor <;> decide
  · decide
  · intro value member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    change 0 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide

private theorem decoding (entry : PooledProgramEntry) (member : entry ∈ program) :
    run (SailRV32.Functions.encdec_backwards entry.bits) before = .ok entry.instruction before := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals with_unfolding_all rfl

private theorem bytes (entry : PooledProgramEntry) (member : entry ∈ program) :
    (Cell.ram entry.pc).read before = .ok entry.bits before := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
    get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
    before, Std.ExtHashMap.getElem_insert]

private theorem fields (entry : PooledProgramEntry) (member : entry ∈ program) :
    Modular.Pooled.decoderFields entry.instruction = some entry.data := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem actual_entry (entry : PooledProgramEntry) (member : entry ∈ program) :
    programEntryRunWith Modular.Pooled.decoderFields before entry.pc = some entry := by
  have read := bytes entry member
  have decode := decoding entry member
  have metadata := fields entry member
  cases entry
  simp only [programEntryRunWith, read, decode, metadata, bind, Option.bind, pure]

theorem actual_public_image : Modular.Pooled.programImage before (program.map ProgramEntry.pc) =
    some program := by
  suffices build : ∀ entries : List PooledProgramEntry,
      (∀ entry ∈ entries, programEntryRunWith Modular.Pooled.decoderFields before entry.pc = some entry) →
      programImageRunWith Modular.Pooled.decoderFields before (entries.map ProgramEntry.pc) = some entries by
    exact build program actual_entry
  intro entries
  induction entries with
  | nil => intro _; rfl
  | cons first rest ih =>
    intro images
    have head := images first (by simp)
    have tail := ih (fun entry member => images entry (by simp [member]))
    change (first.pc :: rest.map ProgramEntry.pc).mapM _ = _
    rw [List.mapM_cons, head]
    change Option.bind ((rest.map ProgramEntry.pc).mapM
      (programEntryRunWith Modular.Pooled.decoderFields before))
      (fun remaining => some (first :: remaining)) = some (first :: rest)
    rw [show (rest.map ProgramEntry.pc).mapM
      (programEntryRunWith Modular.Pooled.decoderFields before) = some rest from tail]
    rfl

private theorem decoded : PooledDecoded trace program := by
  intro actual member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  change ∃ i : Fin 11, _
  refine ⟨index, ?_⟩
  fin_cases index <;> decide

private theorem zero_registers : ∀ index, (Cell.register index).read before = .ok 0 before := by
  have numeric : ∀ index : Nat, index < 32 →
      (Cell.register (BitVec.ofNat 5 index)).read before = .ok 0 before := by
    intro index bound
    interval_cases index
    all_goals first
      | rfl
      | (apply read_register; simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert])
  intro index
  simpa using numeric index.toNat index.isLt

private theorem image : initialImage before cells = some trace.initialMemory := by
  simp only [initialImage, cells, Tests.TraceExecution.cells, List.mapM_cons, List.mapM_nil, zero_registers]
  rfl

private theorem configuration : FlatMemoryConfiguration before := by
  have base := Tests.TraceExecution.configuration
  exact {
    privilege := by simpa [before, Std.ExtDHashMap.get?_insert] using base.privilege
    status := by simpa [before, Std.ExtDHashMap.get?_insert] using base.status
    isa := by simpa [before, Std.ExtDHashMap.get?_insert] using base.isa
    supervisorEnvironment := by simpa [before, Std.ExtDHashMap.get?_insert] using base.supervisorEnvironment
    machineEnvironment := by simpa [before, Std.ExtDHashMap.get?_insert] using base.machineEnvironment
    pmpOff := by simpa [before, Std.ExtDHashMap.get?_insert] using base.pmpOff
    pmpAddresses := by simpa [before, Std.ExtDHashMap.get?_insert] using base.pmpAddresses
    pma := by simpa [before, Std.ExtDHashMap.get?_insert] using base.pma
    hart := by simpa [before, Std.ExtDHashMap.get?_insert] using base.hart
    htifDisabled := by simpa [before, Std.ExtDHashMap.get?_insert] using base.htifDisabled }

private theorem loads : NoDiscardedLoads program := by
  intro entry member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals intros; simp [Modular.instruction]

private theorem inputs : PooledBootInputs trace before cells program Modular.Pooled.decoderFields := by
  refine {
    registers := Tests.TraceExecution.inputs.registers
    ordinary := Tests.TraceExecution.inputs.ordinary
    configuration := configuration
    landingPadDisabled := ?_
    code := ?_
    loads := loads
    distinct := by decide
    aligned := Tests.TraceExecution.inputs.aligned
    programImage := ⟨program.map ProgramEntry.pc, actual_public_image⟩
    profile := ⟨?_, zero_registers, ?_⟩
    seed := rfl
    initialBoundary := rfl
    physicalImage := ⟨seed, image, rfl⟩
    subwordSetup := rfl
    verifierBoundary := ⟨⟨44, (48, 0)⟩,
      VerifierBoundary.Proofs.binding_of_endpoints rfl rfl accepted.states⟩ }
  · refine ⟨0, ?_, rfl⟩
    simp [before, Std.ExtDHashMap.get?_insert]
  · intro entry member
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals constructor <;> decide
  · apply read_register
    simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
  · intro address member _
    simp [cells, Tests.TraceExecution.cells] at member

theorem complete_mixed_trace [MemoryPlatform SailRV32.exception] :
    ∃ after, Relation.ReflTransGen (Modular.Pooled.Step program) before after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 44 after ∧
      (Cell.register 4).read after = .ok 576061442 after := by
  obtain ⟨after, execution, pc, terminal⟩ := Modular.Pooled.native_soundness inputs accepted decoded
  obtain ⟨cell, _, address, read⟩ := terminal (token 4 46 2 8790) (by simp [trace])
  have same : cell = .register 4 := cell_address_injective address
  subst cell
  have value : (ROMView.token before (token 4 46 2 8790)).word.toBitVec = 576061442 := by
    simp only [ROMView.token, ROMView.shadow, token, Cell.addressCode, Nat.unpair_pair,
      Nat.reduceEqDiff, false_and, if_false, MemoryToken.word]
    rfl
  rw [value] at read
  exact ⟨after, execution, pc, read⟩

-- Change only FMAMOD's old destination and the consistently recomputed result.
-- Local arithmetic still holds; initialized matching must reject the fake read.
private def wrongOldAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 31 then 65533 else if column = 33 then 3
  else if column = 37 then 2 else if column = 41 then 576061443
  else assignment 5 column

private def wrongOldRow : Row babyBearModulus PooledFamily := ⟨.addSub, wrongOldAssignment⟩
private def wrongOldTrace : PooledTrace babyBearModulus :=
  { trace with rows := (List.finRange 11).reverse.map fun index =>
      if index = 5 then wrongOldRow else row index }

theorem forged_old_destination_locally_valid : FlatOperation.ConstraintsHoldFlat
    (Verification.environment wrongOldAssignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, wrongOldAssignment, assignment]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)
    | (apply Trace.Proofs.range_contains; decide)

theorem forged_old_destination_rejected : ¬ Accepted wrongOldTrace := by
  intro admitted
  have mismatch : ¬ (wrongOldTrace.initialMemory ++ wrongOldTrace.rows.flatMap Row.writes).Perm
      (wrongOldTrace.terminalMemory ++ wrongOldTrace.rows.flatMap Row.reads) := by decide
  exact mismatch admitted.memory

private def wrongSelectorRow : Row babyBearModulus PooledFamily :=
  ⟨.addSub, fun column => if column = 16 then 0 else if column = 15 then 1 else assignment 5 column⟩

theorem wrong_selector_rejected :
    ¬ PooledDecoded { trace with rows := [wrongSelectorRow] } program := by
  intro admitted
  have queried := admitted wrongSelectorRow (by simp)
  have mismatch : ¬ (decoderTable program .addSub).Contains #[] wrongSelectorRow.decoderQuery := by
    change ¬ ∃ i : Fin 11, _
    decide
  exact mismatch queried

theorem unsupported_mop_rejected :
    Modular.Pooled.decoderFields (.ZIMOP_MOP_RR (4, .Regidx 2, .Regidx 1, .Regidx 3)) = none ∧
    Modular.Pooled.decoderFields (.ZIMOP_MOP_RR (7, .Regidx 2, .Regidx 1, .Regidx 3)) = none := by
  decide

namespace ExternalFixture

-- Replace the public ADDI inputs by independent reads; replace the final
-- discarded modular form by a hint. All native memory accesses remain present.
private def mixedAssignment (index : Fin 11) (column : Nat) : ZMod babyBearModulus :=
  if index = 0 ∨ index = 1 then
    if column = 8 ∨ column = 10 then 0 else if column = 18 then 1 else assignment index column
  else assignment index column

private def mixedRow (index : Fin 11) : Row babyBearModulus PooledFamily := ⟨.addSub, mixedAssignment index⟩

private def entryView (entry : PooledProgramEntry) : PooledProgramEntry :=
  if entry.pc = 0 then ⟨entry.pc, 0x7c0010f3,
    .CSRReg (0x7c0, .Regidx 0, .Regidx 1, .CSRRW),
    { entry.data with immediate := ⟨0, 0⟩, mask := 256 }⟩
  else if entry.pc = 4 then ⟨entry.pc, 0x7c001173,
    .CSRReg (0x7c0, .Regidx 0, .Regidx 2, .CSRRW),
    { entry.data with immediate := ⟨0, 0⟩, mask := 256 }⟩
  else if entry.pc = 36 then ⟨entry.pc, 0x7c009073,
    .CSRReg (0x7c0, .Regidx 1, .Regidx 0, .CSRRW), entry.data⟩
  else entry

private def mixedProgram := program.map entryView
private def mixedBefore : State :=
  { before with
    mem := before.mem
    |>.insert 0 0xf3 |>.insert 1 0x10 |>.insert 2 0 |>.insert 3 0x7c
    |>.insert 4 0x73 |>.insert 5 0x11 |>.insert 6 0 |>.insert 7 0x7c
    |>.insert 36 0x73 |>.insert 37 0x90 |>.insert 38 0 |>.insert 39 0x7c }

private def mixedTrace : PooledTrace babyBearModulus :=
  { trace with
    rows := (List.finRange 11).reverse.map mixedRow
    rom := ⟨ROM.table cells seed, Verification.subwordTable (ROM.words mixedBefore)⟩ }

private theorem mixed_constraints (index : Fin 11) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (mixedAssignment index)) AddSub.clockConstraints := by
  fin_cases index <;>
    simp [AddSub.clockConstraints, AddSub.importedConstraints,
        AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
        Expression.eval, Verification.environment, mixedAssignment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)
    | (apply Trace.Proofs.range_contains; decide)

private theorem mixed_accepted : Accepted mixedTrace := by
  constructor
  · intro actual member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact mixed_constraints index
  · intro actual member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    fin_cases index <;> rfl
  · exact accepted.states
  · exact accepted.memory

private theorem mixed_bytes (entry : PooledProgramEntry) (member : entry ∈ mixedProgram) :
    (Cell.ram entry.pc).read mixedBefore = .ok entry.bits mixedBefore := by
  obtain ⟨original, originalMember, rfl⟩ := (List.mem_map (f := entryView) (l := program)).mp member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at originalMember
  rcases originalMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [entryView, Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
    get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
    mixedBefore, before, Std.ExtHashMap.getElem_insert]

private theorem mixed_decoding (entry : PooledProgramEntry) (member : entry ∈ mixedProgram) :
    run (SailRV32.Functions.encdec_backwards entry.bits) mixedBefore = .ok entry.instruction mixedBefore := by
  obtain ⟨original, originalMember, rfl⟩ := (List.mem_map (f := entryView) (l := program)).mp member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at originalMember
  rcases originalMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals with_unfolding_all rfl

private theorem mixed_fields (entry : PooledProgramEntry) (member : entry ∈ mixedProgram) :
    Modular.External.decoderFields entry.instruction = some entry.data := by
  obtain ⟨original, originalMember, rfl⟩ := (List.mem_map (f := entryView) (l := program)).mp member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at originalMember
  rcases originalMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all rfl

private theorem mixed_entry (entry : PooledProgramEntry) (member : entry ∈ mixedProgram) :
    programEntryRunWith Modular.External.decoderFields mixedBefore entry.pc = some entry := by
  have read := mixed_bytes entry member
  have decode := mixed_decoding entry member
  have metadata := mixed_fields entry member
  cases entry
  simp only [programEntryRunWith, read, decode, metadata, bind, Option.bind, pure]

theorem actual_public_image : Modular.External.programImage mixedBefore (mixedProgram.map ProgramEntry.pc) =
    some mixedProgram := by
  suffices build : ∀ entries : List PooledProgramEntry,
      (∀ entry ∈ entries, programEntryRunWith Modular.External.decoderFields mixedBefore entry.pc = some entry) →
      programImageRunWith Modular.External.decoderFields mixedBefore (entries.map ProgramEntry.pc) = some entries by
    exact build mixedProgram mixed_entry
  intro entries
  induction entries with
  | nil => intro _; rfl
  | cons first rest ih =>
    intro images
    have head := images first (by simp)
    have tail := ih (fun entry member => images entry (by simp [member]))
    change (first.pc :: rest.map ProgramEntry.pc).mapM _ = _
    rw [List.mapM_cons, head]
    change Option.bind ((rest.map ProgramEntry.pc).mapM
      (programEntryRunWith Modular.External.decoderFields mixedBefore))
      (fun remaining => some (first :: remaining)) = some (first :: rest)
    rw [show (rest.map ProgramEntry.pc).mapM
      (programEntryRunWith Modular.External.decoderFields mixedBefore) = some rest from tail]
    rfl

private theorem mixed_decoded : PooledDecoded mixedTrace mixedProgram := by
  intro actual member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  change ∃ i : Fin 11, _
  refine ⟨index, ?_⟩
  fin_cases index <;> decide

private theorem mixed_zero_registers : ∀ index, (Cell.register index).read mixedBefore = .ok 0 mixedBefore := by
  have numeric : ∀ index : Nat, index < 32 →
      (Cell.register (BitVec.ofNat 5 index)).read mixedBefore = .ok 0 mixedBefore := by
    intro index bound
    interval_cases index
    all_goals first
      | rfl
      | (apply read_register; simp [mixedBefore, before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert])
  intro index
  simpa using numeric index.toNat index.isLt

private theorem mixed_image : initialImage mixedBefore cells = some mixedTrace.initialMemory := by
  simp only [initialImage, cells, Tests.TraceExecution.cells, List.mapM_cons, List.mapM_nil, mixed_zero_registers]
  rfl

private theorem mixed_inputs : PooledBootInputs mixedTrace mixedBefore cells mixedProgram Modular.External.decoderFields := by
  refine {
    registers := Tests.TraceExecution.inputs.registers
    ordinary := Tests.TraceExecution.inputs.ordinary
    configuration := {
      privilege := configuration.privilege
      status := configuration.status
      isa := configuration.isa
      supervisorEnvironment := configuration.supervisorEnvironment
      machineEnvironment := configuration.machineEnvironment
      pmpOff := configuration.pmpOff
      pmpAddresses := configuration.pmpAddresses
      pma := configuration.pma
      hart := configuration.hart
      htifDisabled := configuration.htifDisabled }
    landingPadDisabled := ?_
    code := ?_
    loads := ?_
    distinct := by decide
    aligned := Tests.TraceExecution.inputs.aligned
    programImage := ⟨mixedProgram.map ProgramEntry.pc, actual_public_image⟩
    profile := ⟨?_, mixed_zero_registers, ?_⟩
    seed := rfl
    initialBoundary := rfl
    physicalImage := ⟨seed, mixed_image, rfl⟩
    subwordSetup := rfl
    verifierBoundary := ⟨⟨44, (48, 0)⟩,
      VerifierBoundary.Proofs.binding_of_endpoints rfl rfl mixed_accepted.states⟩ }
  · refine ⟨0, ?_, rfl⟩
    simp [mixedBefore, before, Std.ExtDHashMap.get?_insert]
  · intro entry member
    obtain ⟨original, originalMember, rfl⟩ := (List.mem_map (f := entryView) (l := program)).mp member
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at originalMember
    rcases originalMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals constructor <;> decide
  · intro entry member
    obtain ⟨original, originalMember, rfl⟩ := (List.mem_map (f := entryView) (l := program)).mp member
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at originalMember
    rcases originalMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals intros; simp [entryView, Modular.instruction]
  · apply read_register
    simp [mixedBefore, before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
  · intro address member _
    simp [cells, Tests.TraceExecution.cells] at member

private theorem ports : Modular.External.StreamPorts mixedTrace [11, 3, 99] := by
  intro actual member read
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  fin_cases index <;> first | decide | cases read

theorem complete_external_modular_trace [MemoryPlatform SailRV32.exception] :
    ∃ after, Modular.External.ExecutionTrace [11, 3, 99] mixedProgram (mixedBefore, 0) (after, 2) ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 44 after ∧
      (Cell.register 4).read after = .ok 576061442 after := by
  obtain ⟨after, execution, pc, terminal⟩ := Modular.External.native_soundness mixed_inputs mixed_accepted mixed_decoded ports
  obtain ⟨cell, _, address, read⟩ := terminal (token 4 46 2 8790) (by simp [mixedTrace, trace])
  have same : cell = .register 4 := cell_address_injective address
  subst cell
  have value : (ROMView.token mixedBefore (token 4 46 2 8790)).word.toBitVec = 576061442 := by
    simp only [ROMView.token, ROMView.shadow, token, Cell.addressCode, Nat.unpair_pair,
      Nat.reduceEqDiff, false_and, if_false, MemoryToken.word]
    rfl
  rw [value] at read
  exact ⟨after, execution, pc, read⟩

theorem short_stream_rejected : ¬ Modular.External.StreamPorts mixedTrace [11] := by
  intro supplied
  have missing := supplied (mixedRow 1) (by simp [mixedTrace]) (by decide)
  cases missing

theorem wrong_stream_order_rejected : ¬ Modular.External.StreamPorts mixedTrace [3, 11] := by
  intro supplied
  have mismatch := supplied (mixedRow 0) (by simp [mixedTrace]) (by decide)
  have impossible : (3 : BitVec 32) = 11 := Option.some.inj mismatch
  contradiction

end ExternalFixture

end Tests.ModularTrace

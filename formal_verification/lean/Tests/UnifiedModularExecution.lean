import Airbender.Review.Trace.UnifiedReduced.ModularExecution
import Tests.TraceExecution

namespace Tests.UnifiedModularExecution
open Airbender Arithmetic UnifiedReduced Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

-- Native unified rows: dependent modular arithmetic, discarded forms, an
-- ordinary consumer and TRIADD, in reverse physical order.
private def assignment (index : Fin 12) : Nat → ZMod babyBearModulus :=
  match index.val with
  | 0 => fun column => match column with
    | 2 | 30 | 40 => 4
    | 4 | 7 | 11 | 44 | 129 | 130 | 131 | 132 | 133 => 1
    | 8 | 50 => 11
    | 32 => 8
    | _ => 0
  | 1 => fun column => match column with
    | 0 => 4
    | 2 | 30 | 40 => 8
    | 4 | 11 | 129 | 130 | 131 | 132 | 133 => 1
    | 7 | 44 => 2
    | 8 | 50 => 3
    | 32 => 12
    | 34 => 5
    | _ => 0
  | 2 => fun column => match column with
    | 0 => 8
    | 2 | 30 => 12
    | 4 | 5 | 14 | 52 | 129 | 130 | 131 | 132 | 133 => 1
    | 6 | 38 => 2
    | 7 | 42 | 44 => 3
    | 32 => 16
    | 34 => 6
    | 36 => 11
    | 40 => 10
    | 50 => 14
    | 78 => 13
    | 79 => 34816
    | 80 => 943718385
    | _ => 0
  | 3 => fun column => match column with
    | 0 | 40 => 12
    | 2 | 30 | 46 => 16
    | 4 | 6 | 15 | 38 | 52 | 129 | 130 | 131 | 132 | 133 => 1
    | 5 | 7 | 44 | 50 => 3
    | 32 => 20
    | 34 | 36 | 48 => 14
    | 42 => 11
    | 78 => 2
    | 79 => 34816
    | 80 => 377487288
    | _ => 0
  | 4 => fun column => match column with
    | 0 => 16
    | 2 | 30 | 46 => 20
    | 4 | 16 | 52 | 129 | 130 | 131 | 132 | 133 => 1
    | 5 | 7 | 36 | 42 | 44 | 48 => 3
    | 6 | 38 => 2
    | 32 => 24
    | 34 => 18
    | 40 => 13
    | 50 => 65532
    | 51 => 6719
    | 78 => 65531
    | 79 => 41535
    | 80 => 440401916
    | _ => 0
  | 5 => fun column => match column with
    | 0 => 20
    | 2 | 30 | 46 => 24
    | 4 | 17 | 52 | 78 | 129 | 130 | 131 | 132 | 133 => 1
    | 5 | 7 | 42 | 44 => 3
    | 6 | 38 | 50 => 2
    | 32 => 28
    | 34 => 22
    | 36 | 48 => 65532
    | 37 | 49 => 6719
    | 40 => 21
    | 51 => 8790
    | 79 => 43606
    | 80 => 576061442
    | _ => 0
  | 6 => fun column => match column with
    | 0 => 24
    | 2 | 30 | 40 => 28
    | 4 | 11 | 129 | 130 | 131 | 132 | 133 => 1
    | 32 => 32
    | 34 => 9
    | 46 => 29
    | _ => 0
  | 7 => fun column => match column with
    | 0 => 28
    | 2 | 30 | 40 => 32
    | 4 | 11 | 129 | 130 | 131 | 132 | 133 => 1
    | 32 => 36
    | 34 => 30
    | 46 => 33
    | _ => 0
  | 8 => fun column => match column with
    | 0 => 32
    | 2 | 30 | 40 => 36
    | 4 | 11 | 129 | 130 | 131 | 132 | 133 => 1
    | 32 => 40
    | 34 => 34
    | 46 => 37
    | _ => 0
  | 9 => fun column => match column with
    | 0 => 36
    | 2 | 30 | 40 => 40
    | 4 | 11 | 129 | 130 | 131 | 132 | 133 => 1
    | 32 => 44
    | 34 => 38
    | 46 => 41
    | _ => 0
  | 10 => fun column => match column with
    | 0 => 40
    | 2 | 30 => 44
    | 4 | 11 | 129 | 130 | 131 | 132 | 133 => 1
    | 5 => 3
    | 7 | 44 => 4
    | 32 => 48
    | 34 => 26
    | 36 | 50 => 2
    | 37 | 51 => 8790
    | 40 => 42
    | _ => 0
  | 11 => fun column => match column with
    | 0 => 44
    | 2 | 30 => 48
    | 4 | 5 | 20 | 129 | 130 | 131 | 132 | 133 => 1
    | 6 | 38 => 2
    | 7 | 44 => 5
    | 32 => 52
    | 34 => 17
    | 36 => 11
    | 40 => 25
    | 42 => 3
    | 50 => 14
    | 80 => 943718385
    | _ => 0
  | _ => fun _ => 0

private def token (index time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (time, 0), Nat.pair lo hi⟩
private def cells := Tests.TraceExecution.cells
private def seed : List (MemoryToken babyBearModulus) :=
  (List.range 32).map fun index => token index 0 0 0

private def program : List UnifiedReduced.ProgramEntry := [
  ⟨0, 0x00b00093, SailRV32.instruction.ITYPE (11, .Regidx 0, .Regidx 1, .ADDI), ⟨.machine, 0, 0, 1, ⟨11, 0⟩, 1, 0⟩⟩,
  ⟨4, 0x00300113, SailRV32.instruction.ITYPE (3, .Regidx 0, .Regidx 2, .ADDI), ⟨.machine, 0, 0, 2, ⟨3, 0⟩, 1, 0⟩⟩,
  ⟨8, 0x8220c1f3, AddSub.Modular.instruction .add 1 2 3, ⟨.machine, 1, 2, 3, ⟨0, 0⟩, 8, 0⟩⟩,
  ⟨12, 0x8611c1f3, AddSub.Modular.instruction .sub 3 1 3, ⟨.machine, 3, 1, 3, ⟨0, 0⟩, 16, 0⟩⟩,
  ⟨16, 0x8a21c1f3, AddSub.Modular.instruction .mul 3 2 3, ⟨.machine, 3, 2, 3, ⟨0, 0⟩, 32, 0⟩⟩,
  ⟨20, 0x8e21c1f3, AddSub.Modular.instruction .fma 3 2 3, ⟨.machine, 3, 2, 3, ⟨0, 0⟩, 64, 0⟩⟩,
  ⟨24, 0x8220c073, AddSub.Modular.instruction .add 1 2 0, ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩,
  ⟨28, 0x8620c073, AddSub.Modular.instruction .sub 1 2 0, ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩,
  ⟨32, 0x8a20c073, AddSub.Modular.instruction .mul 1 2 0, ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩,
  ⟨36, 0x8e20c073, AddSub.Modular.instruction .fma 1 2 0, ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩,
  ⟨40, 0x00018233, SailRV32.instruction.RTYPE (.Regidx 0, .Regidx 3, .Regidx 4, .ADD), ⟨.machine, 3, 0, 4, ⟨0, 0⟩, 1, 0⟩⟩,
  ⟨44, 0xc220c2f3, .ZIMOP_MOP_RR (4, .Regidx 2, .Regidx 1, .Regidx 5),
    ⟨.machine, 1, 2, 5, ⟨0, 0⟩, 512, 0⟩⟩]

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
      |>.insert 44 (0xf3 : BitVec 8)
      |>.insert 45 (0xc2 : BitVec 8)
      |>.insert 46 (0x20 : BitVec 8)
      |>.insert 47 (0xc2 : BitVec 8)
  }

private def row (index : Fin 12) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment index⟩
private def trace : UnifiedTrace babyBearModulus where
  rows := (List.finRange 12).reverse.map row
  rom := UnifiedReduced.Setup.table before
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 48 (52, 0)
  initialMemory := seed
  terminalMemory := [token 0 45 0 0, token 1 48 11 0, token 2 49 3 0,
    token 3 44 2 8790, token 4 46 2 8790, token 5 50 14 0] ++ seed.drop 6

private theorem constraints (index : Fin 12) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment index)) (clockConstraints trace.rom) := by
  fin_cases index <;> apply Verification.holds_append
  all_goals first
    | (simp [importedConstraints, trace, FlatOperation.ConstraintsHoldFlat,
        Verification.environment, Expression.eval, assignment, Lookup.Contains, Table.toRaw, fromElements]
       repeat' apply And.intro
       all_goals solve
         | decide
         | (apply Verification.range16_contains; decide)
         | (exact ⟨⟨0, by decide⟩, by with_unfolding_all decide⟩))
    | (simp [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
       repeat' apply And.intro
       all_goals apply Trace.Proofs.range_contains
       all_goals simp [Expression.eval, Verification.environment, assignment]
       all_goals decide)

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
  · decide +kernel

private theorem decoding (entry : UnifiedReduced.ProgramEntry) (member : entry ∈ program) :
    run (SailRV32.Functions.encdec_backwards entry.bits) before = .ok entry.instruction before := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals with_unfolding_all rfl

private theorem bytes (entry : UnifiedReduced.ProgramEntry) (member : entry ∈ program) :
    (Cell.ram entry.pc).read before = .ok entry.bits before := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
    get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
    before, Std.ExtHashMap.getElem_insert]

private theorem fields (entry : UnifiedReduced.ProgramEntry) (member : entry ∈ program) :
    UnifiedReduced.Modular.decoderFields entry.instruction = some entry.data := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem actual_entry (entry : UnifiedReduced.ProgramEntry) (member : entry ∈ program) :
    programEntryRunWith UnifiedReduced.Modular.decoderFields before entry.pc = some entry := by
  have read := bytes entry member
  have decode := decoding entry member
  have metadata := fields entry member
  cases entry
  simp only [programEntryRunWith, read, decode, metadata, bind, Option.bind, pure]

theorem actual_public_image : UnifiedReduced.Modular.programImage before (program.map ProgramEntry.pc) =
    some program := by
  suffices build : ∀ entries : List UnifiedReduced.ProgramEntry,
      (∀ entry ∈ entries, programEntryRunWith UnifiedReduced.Modular.decoderFields before entry.pc = some entry) →
      programImageRunWith UnifiedReduced.Modular.decoderFields before (entries.map ProgramEntry.pc) = some entries by
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
      (programEntryRunWith UnifiedReduced.Modular.decoderFields before))
      (fun remaining => some (first :: remaining)) = some (first :: rest)
    rw [show (rest.map ProgramEntry.pc).mapM
      (programEntryRunWith UnifiedReduced.Modular.decoderFields before) = some rest from tail]
    rfl

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

private theorem decoded : UnifiedReduced.Decoded trace program := by
  intro actual member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  change ∃ i : Fin 12, _
  refine ⟨index, ?_⟩
  fin_cases index <;> decide +kernel

private theorem inputs : UnifiedReduced.Modular.Inputs trace before cells program := by
  constructor
  · exact ⟨by decide, Tests.TraceExecution.inputs.aligned,
      ⟨by apply read_register; simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert],
        zero_registers, by intro address member _; simp [cells, Tests.TraceExecution.cells] at member⟩,
      ⟨seed, image⟩, rfl, rfl, ⟨program.map ProgramEntry.pc, actual_public_image⟩, rfl⟩
  · exact Tests.TraceExecution.inputs.registers
  · intro entry member
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals constructor <;> decide
  · exact configuration
  · exact Tests.TraceExecution.inputs.ordinary
  · rintro ⟨entry, member, imm, rs1, rd, encoding⟩
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases encoding
  · intro entry member imm rs1
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AddSub.Modular.instruction]

theorem complete_unified_modular_trace [MemoryPlatform SailRV32.exception] :
    ∃ after, Relation.ReflTransGen (UnifiedReduced.Modular.Step program) before after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 48 after ∧
      (Cell.register 4).read after = .ok 576061442 after ∧
      (Cell.register 5).read after = .ok 14 after := by
  obtain ⟨after, execution, pc, terminal⟩ := UnifiedReduced.Modular.execution_soundness inputs accepted decoded
  have value (index time lo hi : Nat) (present : token index time lo hi ∈ trace.terminalMemory) :
      (Cell.register (BitVec.ofNat 5 index)).read after =
        .ok (Word.mk lo hi).toBitVec after := by
    obtain ⟨cell, _, address, read⟩ := terminal _ present
    have same : cell = .register (BitVec.ofNat 5 index) := Trace.Proofs.cell_address_injective address
    subst cell
    have view : (Trace.ROMView.token before (token index time lo hi)).word = ⟨lo, hi⟩ := by
      simp [Trace.ROMView.token, Trace.ROMView.shadow, token, Cell.addressCode,
        MemoryToken.word, Nat.unpair_pair]
    simpa only [view] using read
  exact ⟨after, execution, pc, value 4 46 2 8790 (by simp [trace]),
    value 5 50 14 0 (by simp [trace])⟩

-- A forged FMA old destination and recomputed result still satisfy the native
-- row equations, but cannot consume the initialized shared register history.
private def forged (column : Nat) : ZMod babyBearModulus :=
  if column = 48 then 65533 else if column = 50 then 3
  else if column = 78 then 2 else if column = 80 then 576061443
  else assignment 5 column

theorem forged_fma_locally_valid : FlatOperation.ConstraintsHoldFlat
    (Verification.environment forged) (clockConstraints trace.rom) := by
  apply Verification.holds_append
  · simp [importedConstraints, trace, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, forged, assignment, Lookup.Contains, Table.toRaw, fromElements]
    repeat' apply And.intro
    all_goals solve
      | decide
      | (apply Verification.range16_contains; decide)
      | (exact ⟨⟨0, by decide⟩, by with_unfolding_all decide⟩)
  · simp [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, forged, assignment]
    all_goals decide

private def forgedTrace : UnifiedTrace babyBearModulus :=
  { trace with rows := trace.rows.map fun actual =>
      if actual.assignment 0 = 20 then ⟨.machine, forged⟩ else actual }

theorem forged_fma_rejected :
    ¬ (forgedTrace.initialMemory ++ forgedTrace.memorySteps.map Prod.snd).Perm
      (forgedTrace.terminalMemory ++ forgedTrace.memorySteps.map Prod.fst) := by decide +kernel

theorem wrong_selector_rejected :
    ¬ (UnifiedReduced.decoderTable program).Contains #[] (decoderQuery (fun column =>
      if column = 14 then 0 else if column = 15 then 1 else assignment 2 column)) := by
  change ¬ ∃ i : Fin 12, _
  decide +kernel

end Tests.UnifiedModularExecution

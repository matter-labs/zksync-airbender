import Tests.AirbenderInitialization
import Airbender.Proofs.Sail.VirtualMemory
import Airbender.Proofs.Sail.Memory
import Airbender.Proofs.Trace.ImageInstall
import Airbender.Proofs.Trace.ProgramConstruction
import Airbender.Review.Trace.Execution

namespace Tests.AirbenderProgram
open Airbender Airbender.Trace Airbender.Arithmetic
open Airbender.Reference Airbender.Reference.Sail Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

/-- Four actual base-ISA encodings: LUI x1,0x2000; ADDI x2,x0,7;
SW x2,0(x1); LW x3,0(x1). All GPRs initially read zero. -/
noncomputable def before : State :=
  wordWriteState (wordWriteState (wordWriteState (wordWriteState
    AirbenderInitialization.before 0 0x020000b7) 4 0x00700113) 8 0x0020a023) 12 0x0000a183

def program : List ProgramEntry :=
  [⟨0, 0x020000b7, .UTYPE (0x02000, .Regidx 1, .LUI),
      ⟨.addSub, 0, 0, 1, ⟨0, 512⟩, 1, 0⟩⟩,
   ⟨4, 0x00700113, .ITYPE (7, .Regidx 0, .Regidx 2, .ADDI),
      ⟨.addSub, 0, 0, 2, ⟨7, 0⟩, 1, 0⟩⟩,
   ⟨8, 0x0020a023, .STORE (0, .Regidx 2, .Regidx 1, 4),
      ⟨.wordMemory, 1, 2, 0, ⟨0, 0⟩, 1, 0⟩⟩,
   ⟨12, 0x0000a183, .LOAD (0, .Regidx 1, .Regidx 3, false, 4),
      ⟨.wordMemory, 1, 0, 3, ⟨0, 0⟩, 0, 0⟩⟩]

private theorem code0 : (Cell.ram 0).read before = .ok 0x020000b7 before := by
  apply written_word_disjoint 12 0x0000a183 (by decide)
  apply written_word_disjoint 8 0x0020a023 (by decide)
  apply written_word_disjoint 4 0x00700113 (by decide)
  exact written_word_read _ _ _

private theorem code4 : (Cell.ram 4).read before = .ok 0x00700113 before := by
  apply written_word_disjoint 12 0x0000a183 (by decide)
  apply written_word_disjoint 8 0x0020a023 (by decide)
  exact written_word_read _ _ _

private theorem code8 : (Cell.ram 8).read before = .ok 0x0020a023 before := by
  apply written_word_disjoint 12 0x0000a183 (by decide)
  exact written_word_read _ _ _

private theorem code12 : (Cell.ram 12).read before = .ok 0x0000a183 before :=
  written_word_read _ _ _

private theorem decode_lui (state : State) :
    run (SailRV32.Functions.encdec_backwards 0x020000b7) state =
      .ok (.UTYPE (0x02000, .Regidx 1, .LUI)) state := by rfl
private theorem decode_addi (state : State) :
    run (SailRV32.Functions.encdec_backwards 0x00700113) state =
      .ok (.ITYPE (7, .Regidx 0, .Regidx 2, .ADDI)) state := by rfl
private theorem decode_sw (state : State) :
    run (SailRV32.Functions.encdec_backwards 0x0020a023) state =
      .ok (.STORE (0, .Regidx 2, .Regidx 1, 4)) state := by rfl
private theorem decode_lw (state : State) :
    run (SailRV32.Functions.encdec_backwards 0x0000a183) state =
      .ok (.LOAD (0, .Regidx 1, .Regidx 3, false, 4)) state := by rfl

/-- Actual initialized bytes, unchanged upstream decoding and native metadata. -/
theorem program_image : programImageRunWith decoderFields before [0, 4, 8, 12] = some program := by
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith,
    code0, code4, code8, code12, decode_lui before, decode_addi before,
    decode_sw before, decode_lw before, bind, Option.bind]
  rfl

/-- The same original instructions can be projected into the pooled or inline
native registry without rebuilding or assuming the decoded program. -/
theorem mapped_program_image {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (map : DecoderData → DecoderData Kind)
    (fields : ∀ entry ∈ program, projection entry.instruction = some (map entry.data)) :
    programImageRunWith projection before [0, 4, 8, 12] =
      some (program.map fun entry => ⟨entry.pc, entry.bits, entry.instruction, map entry.data⟩) := by
  have f0 : projection (.UTYPE (0x02000, .Regidx 1, .LUI)) =
      some (map ⟨.addSub, 0, 0, 1, ⟨0, 512⟩, 1, 0⟩) := fields program[0] (by simp [program])
  have f1 : projection (.ITYPE (7, .Regidx 0, .Regidx 2, .ADDI)) =
      some (map ⟨.addSub, 0, 0, 2, ⟨7, 0⟩, 1, 0⟩) := fields program[1] (by simp [program])
  have f2 : projection (.STORE (0, .Regidx 2, .Regidx 1, 4)) =
      some (map ⟨.wordMemory, 1, 2, 0, ⟨0, 0⟩, 1, 0⟩) := fields program[2] (by simp [program])
  have f3 : projection (.LOAD (0, .Regidx 1, .Regidx 3, false, 4)) =
      some (map ⟨.wordMemory, 1, 0, 3, ⟨0, 0⟩, 0, 0⟩) := fields program[3] (by simp [program])
  have e0 := Trace.Proofs.program_entry_run_of_reads projection before 0 0x020000b7
    (.UTYPE (0x02000, .Regidx 1, .LUI)) _ code0 (decode_lui before) f0
  have e1 := Trace.Proofs.program_entry_run_of_reads projection before 4 0x00700113
    (.ITYPE (7, .Regidx 0, .Regidx 2, .ADDI)) _ code4 (decode_addi before) f1
  have e2 := Trace.Proofs.program_entry_run_of_reads projection before 8 0x0020a023
    (.STORE (0, .Regidx 2, .Regidx 1, 4)) _ code8 (decode_sw before) f2
  have e3 := Trace.Proofs.program_entry_run_of_reads projection before 12 0x0000a183
    (.LOAD (0, .Regidx 1, .Regidx 3, false, 4)) _ code12 (decode_lw before) f3
  simp only [programImageRunWith, List.mapM_cons, List.mapM_nil, e0, e1, e2, e3,
    bind, Option.bind, pure]
  rfl

theorem physical_image {domain : List Cell} {image : List (MemoryToken babyBearModulus)}
    (source : initialImage AirbenderInitialization.before domain = some image)
    (aligned : ∀ cell ∈ domain, cell.Aligned) :
    ∃ physical : List (MemoryToken babyBearModulus), initialImage before domain = some physical := by
  obtain ⟨first, initial⟩ := Trace.Proofs.image_word_write_exists source aligned 0 (by decide) 0x020000b7
  obtain ⟨second, next⟩ := Trace.Proofs.image_word_write_exists initial aligned 4 (by decide) 0x00700113
  obtain ⟨third, thenNext⟩ := Trace.Proofs.image_word_write_exists next aligned 8 (by decide) 0x0020a023
  exact Trace.Proofs.image_word_write_exists thenNext aligned 12 (by decide) 0x0000a183

theorem configuration : FlatMemoryConfiguration before :=
  configuration_word_write (configuration_word_write (configuration_word_write
    (configuration_word_write AirbenderInitialization.configuration _ _) _ _) _ _) _ _

theorem registers_zero (index : BitVec 5) :
    (Cell.register index).read before = .ok 0 before :=
  rX_register_frame (before := AirbenderInitialization.before) (after := before) rfl index
    (AirbenderInitialization.registers_zero index)

/-- ROM installation changes physical fetch bytes, while native ROM-shadow
initial tokens remain zero. Non-ROM RAM retains the public zero boot profile. -/
theorem initial_profile (domain : List Cell)
    (profile : InitialProfile AirbenderInitialization.before domain) : InitialProfile before domain := by
  refine ⟨?_, registers_zero, ?_⟩
  · have original := profile.pc
    change run (SailRV32.readReg .PC) AirbenderInitialization.before =
      .ok 0 AirbenderInitialization.before at original
    apply read_register
    change AirbenderInitialization.before.regs.get? .PC = some 0
    exact read_register_iff.mp original
  · intro address member nonROM
    have lower : 16 ≤ address.toNat := by dsimp [ROM.limit] at nonROM; omega
    apply written_word_disjoint 12 0x0000a183 (Or.inr lower)
    apply written_word_disjoint 8 0x0020a023 (Or.inr (by omega))
    apply written_word_disjoint 4 0x00700113 (Or.inr (by omega))
    apply written_word_disjoint 0 0x020000b7 (Or.inr (by omega))
    exact profile.ram address member nonROM

private def prepare (state : State) (pc : BitVec 32) : State :=
  { state with regs := state.regs.insert .nextPC pc }
private def finish (state : State) (pc : BitVec 32) : State :=
  { state with regs := state.regs.insert .PC pc }
private def destination (state : State) (reg : SailRV32.Register)
    (value : SailRV32.RegisterType reg) : State :=
  { state with regs := state.regs.insert reg value }

noncomputable def afterLUI : State := finish (destination (prepare before 4) .x1 33554432) 4
noncomputable def afterADDI : State := finish (destination (prepare afterLUI 8) .x2 7) 8
noncomputable def afterSW : State := finish (wordWriteState (prepare afterADDI 12) 33554432 7) 12
noncomputable def afterLW : State := finish (destination (prepare afterSW 16) .x3 7) 16

private theorem write_one (state : State) (value : BitVec 32) :
    run (SailRV32.Functions.wX_bits (.Regidx 1) value) state =
      .ok () (destination state .x1 value) := by
  simp [SailRV32.Functions.wX_bits, SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, destination]
  rfl

private theorem write_two (state : State) (value : BitVec 32) :
    run (SailRV32.Functions.wX_bits (.Regidx 2) value) state =
      .ok () (destination state .x2 value) := by
  simp [SailRV32.Functions.wX_bits, SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, destination]
  rfl

private theorem write_three (state : State) (value : BitVec 32) :
    run (SailRV32.Functions.wX_bits (.Regidx 3) value) state =
      .ok () (destination state .x3 value) := by
  simp [SailRV32.Functions.wX_bits, SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, destination]
  rfl

private theorem normal {state executed : State} {pc : BitVec 32}
    (clause : SailRV32.SailM SailRV32.ExecutionResult)
    (current : run (SailRV32.Functions.get_arch_pc ()) state = .ok pc state)
    (execution : run clause (prepare state (pc + 4)) =
      .ok SailRV32.Functions.RETIRE_SUCCESS executed)
    (next : executed.regs.get? .nextPC = some (pc + 4)) :
    run (normalStep clause) state =
      .ok SailRV32.Functions.RETIRE_SUCCESS (finish executed (pc + 4)) := by
  simp only [normalStep]
  rw [run_bind_of_ok _ _ _ _ _ (initialize_next_pc current)]
  dsimp only [prepare] at execution
  rw [run_bind_of_ok _ _ _ _ _ execution]
  rw [run_bind_of_ok _ _ _ _ _ (tick_pc_run next)]
  rfl

private theorem lui : run (normalStep (SailRV32.Functions.execute_UTYPE
    0x02000 (.Regidx 1) .LUI)) before = .ok SailRV32.Functions.RETIRE_SUCCESS afterLUI := by
  apply normal (pc := 0) (executed := destination (prepare before 4) .x1 33554432)
  · exact (initial_profile [] ⟨AirbenderInitialization.standalone_profile.profile.pc,
      AirbenderInitialization.registers_zero, by simp⟩).pc
  · simp only [SailRV32.Functions.execute_UTYPE, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ (write_one _ _)]
    rfl
  · simp [destination, prepare, Std.ExtDHashMap.get?_insert]

private theorem addi : run (normalStep (SailRV32.Functions.execute_ITYPE
    7 (.Regidx 0) (.Regidx 2) .ADDI)) afterLUI = .ok SailRV32.Functions.RETIRE_SUCCESS afterADDI := by
  apply normal (pc := 4) (executed := destination (prepare afterLUI 8) .x2 7)
  · apply read_register
    simp [afterLUI, finish]
  · have zero : run (SailRV32.Functions.rX_bits (.Regidx 0)) (prepare afterLUI (4 + 4)) =
        .ok 0 (prepare afterLUI (4 + 4)) := rfl
    simp only [SailRV32.Functions.execute_ITYPE, freeM_bind_assoc, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ zero]
    rw [run_bind_of_ok _ _ _ _ _ (write_two _ _)]
    rfl
  · simp [destination, prepare, Std.ExtDHashMap.get?_insert]

private theorem configuredADDI : FlatMemoryConfiguration afterADDI := by
  apply configuration_pc_write
  apply configuration_gpr_write (configuration_next_pc_write
    (configuration_pc_write (configuration_gpr_write
      (configuration_next_pc_write configuration 4) 1 33554432 (write_one _ _)) 4) 8) 2 7
  exact write_two _ _

private theorem sourceSW : run (SailRV32.Functions.rX_bits (.Regidx 1))
    (prepare afterADDI 12) = .ok 33554432 (prepare afterADDI 12) := by
  apply read_register
  simp [prepare, afterADDI, afterLUI, finish, destination, Std.ExtDHashMap.get?_insert]

private theorem sw : run (normalStep (SailRV32.Functions.execute_STORE
    0 (.Regidx 2) (.Regidx 1) 4)) afterADDI = .ok SailRV32.Functions.RETIRE_SUCCESS afterSW := by
  apply normal (pc := 8) (executed := wordWriteState (prepare afterADDI 12) 33554432 7)
  · apply read_register
    simp [afterADDI, finish]
  · apply store_word (before := prepare afterADDI 12)
      (after := wordWriteState (prepare afterADDI 12) 33554432 7)
      (imm := 0) (rs1 := .Regidx 1) (rs2 := .Regidx 2) (value := 7)
    · apply read_register
      simp [prepare, afterADDI, finish, destination, Std.ExtDHashMap.get?_insert]
    · exact virtual_word_write_platform (before := prepare afterADDI 12) (source := 33554432)
        (configuration_next_pc_write configuredADDI 12) (.Regidx 1) 0 sourceSW
        (by decide) (ordinaryWordAddress_airbender _) 7
  · simp [wordWriteState, prepare]

private theorem lw : run (normalStep (SailRV32.Functions.execute_LOAD
    0 (.Regidx 1) (.Regidx 3) false 4)) afterSW = .ok SailRV32.Functions.RETIRE_SUCCESS afterLW := by
  apply normal (pc := 12) (executed := destination (prepare afterSW 16) .x3 7)
  · apply read_register
    simp [afterSW, finish]
  · have source : run (SailRV32.Functions.rX_bits (.Regidx 1)) (prepare afterSW 16) =
        .ok 33554432 (prepare afterSW 16) := by
      apply read_register
      simp [prepare, afterSW, finish, wordWriteState, afterADDI, afterLUI,
        destination, Std.ExtDHashMap.get?_insert]
    have config : FlatMemoryConfiguration (prepare afterSW 16) :=
      configuration_next_pc_write (configuration_pc_write
        (configuration_word_write (configuration_next_pc_write configuredADDI 12) 33554432 7) 12) 16
    have bytes : (readBytes (ue := SailRV32.exception) 4 33554432).run (prepare afterSW 16) =
        .ok (7 : BitVec 32) (prepare afterSW 16) :=
      read_word_frame (before := wordWriteState (prepare afterADDI 12) 33554432 7)
        (after := prepare afterSW 16) rfl (written_word_read (prepare afterADDI 12) 33554432 7)
    have memory := virtual_word_read_platform (before := prepare afterSW 16)
      (source := 33554432) (value := 7) config (.Regidx 1) 0 source
      (by decide) (ordinaryWordAddress_airbender _) bytes
    change run (SailRV32.Functions.execute_LOAD 0 (.Regidx 1) (.Regidx 3) false 4)
      (prepare afterSW 16) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (destination (prepare afterSW 16) .x3 7)
    rw [load_word (before := prepare afterSW 16) (imm := 0)
      (rs1 := .Regidx 1) (rd := .Regidx 3) (value := 7) memory]
    rw [run_bind_of_ok _ _ _ _ _ (write_three _ _)]
    rfl
  · simp [destination, prepare, Std.ExtDHashMap.get?_insert]

/-- Original Sail execution performs the real store and subsequent load in the
CLINT address region. No read, output or successful-execution premise is supplied. -/
theorem original_execution :
    run (do let _ ← normalStep (SailRV32.Functions.execute_UTYPE 0x02000 (.Regidx 1) .LUI)
            let _ ← normalStep (SailRV32.Functions.execute_ITYPE 7 (.Regidx 0) (.Regidx 2) .ADDI)
            let _ ← normalStep (SailRV32.Functions.execute_STORE 0 (.Regidx 2) (.Regidx 1) 4)
            normalStep (SailRV32.Functions.execute_LOAD 0 (.Regidx 1) (.Regidx 3) false 4)) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS afterLW := by
  rw [run_bind_of_ok _ _ _ _ _ lui, run_bind_of_ok _ _ _ _ _ addi,
    run_bind_of_ok _ _ _ _ _ sw]
  exact lw

/-- Fetch, original decoder, original clause selection and real PC retirement
are checked at each of the four program entries, including after the RAM write. -/
theorem decoded_execution :
    Relation.ReflTransGen (StepWith decoderFields instructionClause program) before afterLW := by
  have first : StepWith decoderFields instructionClause program before afterLUI := by
    refine ⟨program[0], by simp [program], ⟨code0, decode_lui before, rfl⟩, ?_, _, rfl, lui⟩
    exact (initial_profile [] ⟨AirbenderInitialization.standalone_profile.profile.pc,
      AirbenderInitialization.registers_zero, by simp⟩).pc
  have second : StepWith decoderFields instructionClause program afterLUI afterADDI := by
    refine ⟨program[1], by simp [program], ⟨?_, decode_addi afterLUI, rfl⟩, ?_, _, rfl, addi⟩
    · change (readBytes (ue := SailRV32.exception) 4 4).run afterLUI = .ok 0x00700113 afterLUI
      exact read_word_frame (before := before) (after := afterLUI) rfl code4
    · change run (SailRV32.Functions.get_arch_pc ()) afterLUI = .ok 4 afterLUI
      apply read_register; simp [afterLUI, finish]
  have third : StepWith decoderFields instructionClause program afterADDI afterSW := by
    refine ⟨program[2], by simp [program], ⟨?_, decode_sw afterADDI, rfl⟩, ?_, _, rfl, sw⟩
    · change (readBytes (ue := SailRV32.exception) 4 8).run afterADDI = .ok 0x0020a023 afterADDI
      exact read_word_frame (before := before) (after := afterADDI) rfl code8
    · change run (SailRV32.Functions.get_arch_pc ()) afterADDI = .ok 8 afterADDI
      apply read_register; simp [afterADDI, finish]
  have fourth : StepWith decoderFields instructionClause program afterSW afterLW := by
    refine ⟨program[3], by simp [program], ⟨?_, decode_lw afterSW, rfl⟩, ?_, _, rfl, lw⟩
    · change (readBytes (ue := SailRV32.exception) 4 12).run afterSW = .ok 0x0000a183 afterSW
      apply read_word_frame (before := wordWriteState (prepare afterADDI 12) 33554432 7)
        (after := afterSW) rfl
      apply written_word_disjoint 33554432 7 (Or.inl (by decide))
      exact read_word_frame (before := before) (after := prepare afterADDI 12) rfl code12
    · change run (SailRV32.Functions.get_arch_pc ()) afterSW = .ok 12 afterSW
      apply read_register; simp [afterSW, finish]
  exact (Relation.ReflTransGen.single first).trans
    ((Relation.ReflTransGen.single second).trans
      ((Relation.ReflTransGen.single third).trans (Relation.ReflTransGen.single fourth)))

/-- Terminal observations are obtained from the concrete runtime state. -/
theorem terminal :
    run (SailRV32.Functions.get_arch_pc ()) afterLW = .ok 16 afterLW ∧
    (Cell.register 1).read afterLW = .ok 33554432 afterLW ∧
    (Cell.register 2).read afterLW = .ok 7 afterLW ∧
    (Cell.register 3).read afterLW = .ok 7 afterLW ∧
    (Cell.ram 33554432).read afterLW = .ok 7 afterLW := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply read_register; simp [afterLW, finish]
  · apply read_register
    simp [afterLW, afterSW, afterADDI, afterLUI, prepare, finish, destination,
      wordWriteState, Std.ExtDHashMap.get?_insert]
  · apply read_register
    simp [afterLW, afterSW, afterADDI, prepare, finish, destination,
      wordWriteState, Std.ExtDHashMap.get?_insert]
  · apply read_register
    simp [afterLW, finish, destination, Std.ExtDHashMap.get?_insert]
  · exact read_word_frame (before := wordWriteState (prepare afterADDI 12) 33554432 7)
        (after := afterLW) rfl (written_word_read (prepare afterADDI 12) 33554432 7)

end Tests.AirbenderProgram

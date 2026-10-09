import Airbender.Proofs.JumpBranchSlt.Values
import Airbender.Proofs.JumpBranchSlt.PortReads
import Airbender.Proofs.JumpBranchSlt.JumpSoundness
import Airbender.Proofs.Trace.Retirement

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- An actual public-decoded JAL/JALR row executes Sail's original clause and
    retirement. Register ranges/reads, selectors and PC reads are derived.
    Canonical termination and Machine/MLPE configuration remain boundaries. -/
theorem local_jump_execution {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (active : w 4 = 1) {initial : State} {cells : List Cell} (epoch : Nat)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (sourceBound : (Word.mk (w 22).val (w 23).val).Bounded)
    (initialAligned : (w 0).val % 4 = 0) (finalHiBound : (w 17).val < limbBase)
    (instruction : Jump.Instruction) (rs1 rd : BitVec 5)
    (encoding : entry.instruction = match instruction with
      | .jal imm => .JAL (imm, .Regidx rd)
      | .jalr imm => .JALR (imm, .Regidx rs1, .Regidx rd))
    {before after : State} {events : List MemoryAccess}
    (history : Trace.Proofs.SailHistory cells (nativeEvents epoch w).reverse before after)
    (past : Trace.Proofs.SailHistory cells events initial before)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : instruction.indirect = true →
      initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0) :
    let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
    let finalPC := (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec
    run (normalStep (match instruction with
      | .jal imm => SailRV32.Functions.execute_JAL imm (.Regidx rd)
      | .jalr imm => SailRV32.Functions.execute_JALR imm (.Regidx rs1) (.Regidx rd)))
      (Trace.Proofs.retiredState before currentPC) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (Trace.Proofs.retiredState after finalPC) := by
  let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
  let finalPC := (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec
  let rebased := Trace.Proofs.retiredState before currentPC
  let finished := Trace.Proofs.retiredState after currentPC
  have history' := Trace.Proofs.retired_state_history history currentPC
  have csrs := Trace.Proofs.sail_history_control_flow_csrs past
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  let data : DecoderData Unit := match instruction with
    | .jal imm => ⟨(), 0, 0, rd, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),
        if rd = 0 then 17 else 1, 0⟩
    | .jalr imm => ⟨(), rs1, 0, rd, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),
        if rd = 0 then 18 else 2, 0⟩
  have shape : entry.data = data := by
    have fields := source.fields
    rw [encoding] at fields
    cases instruction <;> simp only [decoderFields] at fields <;> exact (Option.some.inj fields).symm
  have fields := decoder_field_bounds source.fields
  have flags := decoder_selectors limbField h fields.2.1 query
  have f0 := flags ⟨0, by decide⟩
  have f1 := flags ⟨1, by decide⟩
  have f2 := flags ⟨2, by decide⟩
  have f3 := flags ⟨3, by decide⟩
  have f4 := flags ⟨4, by decide⟩
  have selectors : w 11 = (if instruction.indirect then 0 else 1) ∧
      w 12 = (if instruction.indirect then 1 else 0) ∧ w 13 = 0 ∧ w 14 = 0 ∧
      w 15 = if rd = 0 then 1 else 0 := by
    by_cases zero : rd = 0
    all_goals cases instruction <;>
      simp_all [importedConstraintsDecoderColumns, data, Nat.testBit, Jump.Instruction.indirect]
  have canonical := Trace.Proofs.native_query_pc_word limbField query
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at canonical
  have pcBound : (Word.mk (w 0).val (w 1).val).Bounded :=
    canonical.symm ▸ Word.ofBitVec_bound entry.pc
  have indices := Trace.Proofs.native_query_indices limbField query
  have leftIndex : w 5 = (entry.data.rs1.toNat : ZMod p) := by
    have index := indices.1
    change (w 5).val = entry.data.rs1.toNat at index
    exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have rdIndex : w 7 = (rd.toNat : ZMod p) := by
    have index := indices.2.2
    change (w 7).val = entry.data.rd.toNat at index
    rw [shape] at index
    cases instruction <;>
      exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
  change w 8 = (entry.data.immediate.lo : ZMod p) at low
  change w 9 = (entry.data.immediate.hi : ZMod p) at high
  let input : Jump.Input := ⟨instruction, ⟨(w 22).val, (w 23).val⟩,
    entry.data.immediate, ⟨(w 0).val, (w 1).val⟩, .Regidx rs1, .Regidx rd, rebased⟩
  let output : Output := ⟨⟨(w 30).val, (w 31).val⟩, ⟨(w 16).val, (w 17).val⟩⟩
  have mapping : Jump.WordMapping input output w := by
    constructor
    · exact ⟨rfl, rfl⟩
    · cases instruction <;> exact ⟨rfl, rfl, low, high, rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · intro indirect
      cases instruction
      case jal => simp [input, Jump.Instruction.indirect] at indirect
      case jalr => simpa [input, shape, data] using leftIndex
    · exact rdIndex
  have read := register_reads limbField epoch query history' ⟨0, by decide⟩
  have interface : Jump.InterfaceAssumptions input output w := by
    constructor
    · exact active
    · exact ⟨selectors.1, selectors.2.1⟩
    · exact ⟨selectors.2.2.1, selectors.2.2.2.1⟩
    · change w 15 = 1 ↔ .Regidx rd = zeroRegister
      rw [selectors.2.2.2.2]
      by_cases zero : rd = 0 <;> simp [zero, zeroRegister]
    · exact pcBound.1
    · cases instruction
      case jal => exact pcBound.1
      case jalr => exact sourceBound.1
    · intro indirect
      cases instruction
      case jal => simp [input, Jump.Instruction.indirect] at indirect
      case jalr => exact sourceBound.2
    · exact fields.1
    · intro direct
      cases instruction
      case jal =>
        have lowEven : (w 0).val % 2 = 0 := by
          have twice : ((w 0).val % 4) % 2 = 0 := by rw [initialAligned]
          rwa [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)] at twice
        exact ⟨lowEven, by simpa [encoding] using decoder_offset_even source⟩
      case jalr => simp [input, Jump.Instruction.indirect] at direct
    · exact finalHiBound
    · change entry.data.immediate.toBitVec = _
      rw [shape]
      cases instruction <;> exact Word.ofBitVec_roundtrip _
    · intro indirect
      cases instruction
      case jal => simp [input, Jump.Instruction.indirect] at indirect
      case jalr =>
        simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.readCode,
          pairCode, Trace.Proofs.memoryWord, input] using read
    · exact Trace.Proofs.retired_state_pc before currentPC
    · obtain ⟨value, read⟩ := isa
      refine ⟨value, read_register ?_⟩
      simpa [input, rebased, Trace.Proofs.retiredState, Std.ExtDHashMap.get?_insert] using csrs.1.trans read
    · intro indirect
      obtain ⟨privilege, security, securityRead, landingPad⟩ := configuration indirect
      constructor
      · apply read_register
        simpa [input, rebased, Trace.Proofs.retiredState, Std.ExtDHashMap.get?_insert]
          using csrs.2.1.trans privilege
      · refine ⟨security, read_register ?_, landingPad⟩
        simpa [input, rebased, Trace.Proofs.retiredState, Std.ExtDHashMap.get?_insert]
          using csrs.2.2.trans securityRead
  obtain ⟨checkedAfter, normal, projected⟩ := jump_soundness hp input output w
    ⟨interface, h, mapping⟩
  have written := register_write limbField epoch query history'
  have write : run (SailRV32.Functions.wX_bits (.Regidx rd) output.destination.toBitVec) rebased =
      .ok () finished := by
    cases instruction <;> simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.writeCode,
      pairCode, Trace.Proofs.memoryWord, output] using written
  have nativeProjection := Trace.Proofs.projected_step_of_write rd output write
  have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
  rw [same] at normal
  cases instruction <;> simpa only [Jump.execution, input, output, rebased, finished,
    Trace.Proofs.retired_state_overwrite] using normal

theorem jump_rebased_step {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : JumpBranchSlt.programImage initial addresses = some program)
    (decoded : Decoded trace program) (terminal : trace.terminal.word.Bounded)
    (initialAligned : trace.initial.word.lo % 4 = 0)
    {w : Nat → ZMod p} (member : (⟨.jumpBranchSlt, w⟩ : Row p TraceKind) ∈ trace.rows)
    {entry : ProgramEntry} (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (instruction : Jump.Instruction) (rs1 rd : BitVec 5)
    (encoding : entry.instruction = match instruction with
      | .jal imm => .JAL (imm, .Regidx rd)
      | .jalr imm => .JALR (imm, .Regidx rs1, .Regidx rd))
    {before after : State} {events : List MemoryAccess}
    (history : Trace.Proofs.SailHistory cells (nativeEvents trace.memoryEpoch w).reverse before after)
    (past : Trace.Proofs.SailHistory cells events initial before)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : instruction.indirect = true →
      initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0) :
    let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
    let finalPC := (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec
    run (normalStep (match instruction with
      | .jal imm => SailRV32.Functions.execute_JAL imm (.Regidx rd)
      | .jalr imm => SailRV32.Functions.execute_JALR imm (.Regidx rs1) (.Regidx rd)))
      (Trace.Proofs.retiredState before currentPC) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (Trace.Proofs.retiredState after finalPC) := by
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have source := Trace.Proofs.program_sources programImage entry present
  have bounds := (native_value_bounds hp inverse accepted clocks image programImage decoded).1 _ member
  have left := bounds importedConstraintsMemoryPorts[0]
    (by simp [Row.ports, importedConstraintsMemoryPorts])
  have leftBound : (Word.mk (w 22).val (w 23).val).Bounded := by
    simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts] using left
  have finalHi := (trace_pc_bounds limbField accepted decoded terminal _ member).2.2
  have aligned := ((trace_pc_alignment hp accepted initialAligned).1 _ member).1
  exact local_jump_execution hp h (accepted.active _ member) trace.memoryEpoch source query
    leftBound aligned finalHi instruction rs1 rd encoding history past isa configuration

end Airbender.JumpBranchSlt.Proofs

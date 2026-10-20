import Human.Circuits.UnifiedReduced.Jump
import Slop.UnifiedReduced.JumpArithmetic
import Slop.UnifiedReduced.RegisterReads
import Slop.Sail.JumpRetirement
import Slop.JumpBranchSlt.Decoder

namespace Airbender.UnifiedReduced.Jump.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def metadata (input : Input) : DecoderData UnifiedFamily :=
  ⟨.machine, if input.instruction.indirect then (match input.rs1 with | .Regidx bits => bits) else 0,
    0, match input.rd with | .Regidx bits => bits,
    Word.ofBitVec (match input.instruction with
      | .jal imm => SailRV32.Functions.sign_extend (m := 32) imm
      | .jalr imm => SailRV32.Functions.sign_extend (m := 32) imm),
    (if input.instruction.indirect then 2048 else 1024) +
      (if input.rd = zeroRegister then 16384 else 0), 0⟩

private theorem decoded_metadata {input : Input} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = instruction input) : entry.data = metadata input := by
  rw [encoding] at fields
  rcases input with ⟨kind, source, offset, pc, ⟨rs1⟩, ⟨rd⟩, before⟩
  change BitVec 5 at rs1 rd
  cases kind <;> by_cases zero : rd = (0#5)
  all_goals simpa [instruction, JumpBranchSlt.Jump.instruction, decoderFields, Trace.decoderFields, JumpBranchSlt.decoderFields,
    jumpFields, DecoderData.mapFamily, metadata, JumpBranchSlt.Jump.Instruction.indirect,
    zeroRegister, zero] using fields.symm

theorem soundness_from_history [Fact p.Prime] (hp : 4194304 ≤ p)
    {setup : Table (ZMod p) (fields 10)} {initial : State} {cells : List Cell} {events : List MemoryAccess}
    {input : Input} {output : Output} {w : Nat → ZMod p} {after : State} {epoch : Nat}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (setupBinding : setup = Setup.table initial)
    (past : SailHistory cells events (retiredState initial input.pc.toBitVec) input.before)
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse input.before after)
    (leftRange : (readToken w importedConstraintsMemoryPorts[0]).word.Bounded)
    (words : WordMapping input output w)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query) (encoding : entry.instruction = instruction input)
    (codeAligned : entry.pc.toNat % 4 = 0)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (landingPad : input.instruction.indirect = true →
      initial.regs.get? .cur_privilege = some .Machine ∧
        ∃ security, initial.regs.get? .mseccfg = some security ∧
          SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before) :
    JumpBranchSlt.Jump.spec input output := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have fields := decoded_metadata source.fields encoding
  have flags := UnifiedReduced.Proofs.decoder_selectors (by omega) core
    (UnifiedReduced.Proofs.decoder_field_bounds source.fields).2.1 query
  have flag (i : Fin 19) := flags i
  rw [fields] at flag
  have selected : w 21 = (if input.instruction.indirect then 0 else 1) ∧
      w 22 = (if input.instruction.indirect then 1 else 0) := by
    have a := flag 10; have b := flag 11
    cases kind : input.instruction <;> by_cases zero : input.rd = zeroRegister
    all_goals simp [metadata, kind, zero, JumpBranchSlt.Jump.Instruction.indirect,
      importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] at a b ⊢
    all_goals exact ⟨a, b⟩
  have excluded (i : Fin 19) (different : i ≠ 10 ∧ i ≠ 11 ∧ i ≠ 14) :
      w importedConstraintsDecoderColumns.flags[i] = 0 := by
    have bit := flag i
    cases kind : input.instruction <;> by_cases zero : input.rd = zeroRegister
    all_goals fin_cases i
    all_goals solve | simp at different | simpa [metadata, kind, zero, importedConstraintsDecoderColumns,
      JumpBranchSlt.Jump.Instruction.indirect, Nat.testBit, Nat.shiftRight_eq_div_pow] using bit
  have other : w 23 = 0 ∧ w 24 = 0 := ⟨excluded 12 (by decide), excluded 13 (by decide)⟩
  have binary : w 26 = 0 ∧ w 27 = 0 := ⟨excluded 15 (by decide), excluded 16 (by decide)⟩
  have noLoad : w 28 = 0 := excluded 17 (by decide)
  have gate := Verification.assertion_of_holds core ⟨42, by rw [constraint_count]; decide⟩
  have noROM : w 87 = 0 := by
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, noLoad] using gate
  have mask : w 25 = if input.rd = zeroRegister then 1 else 0 := by
    have bit := flag 14
    cases kind : input.instruction <;> by_cases zero : input.rd = zeroRegister
    all_goals simpa [metadata, kind, zero, JumpBranchSlt.Jump.Instruction.indirect,
      importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using bit
  have canonical := native_query_pc_word limbSize query
  change initialPC w = Word.ofBitVec entry.pc at canonical
  have pcBound : input.pc.Bounded := by rw [words.pc, canonical]; exact Word.ofBitVec_bound _
  have offset : input.offset = (metadata input).immediate := by
    rw [words.offset]
    exact (native_query_immediate_word limbSize
      (UnifiedReduced.Proofs.decoder_field_bounds source.fields).1 query).trans (congrArg DecoderData.immediate fields)
  have offsetBound : input.offset.Bounded := by rw [offset]; exact Word.ofBitVec_bound _
  have sourceBound : input.source.Bounded := by
    simpa [words.source, readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code,
      pairCode, importedConstraintsMemoryPorts, sourceWord] using leftRange
  have registers := UnifiedReduced.Proofs.register_reads limbSize core noLoad query epoch history
  rw [fields] at registers
  have sourceRead : input.instruction.indirect = true →
      run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.source.toBitVec input.before := by
    intro indirect
    cases first : input.rs1
    simpa [metadata, indirect, first, words.source, sourceWord] using registers.1
  have sum : w 21 + w 22 = 1 := by cases mode : input.instruction.indirect <;> simp [selected.1, selected.2, mode]
  have nativePCBound : (Word.mk (w 0).val (w 1).val).Bounded := by
    simpa [words.pc, initialPC] using pcBound
  have link := UnifiedReduced.Proofs.jump_link (by omega) core sum other nativePCBound
  have link : output.destination.toBitVec = if input.rd = zeroRegister then 0 else input.pc.toBitVec + 4 := by
    rw [words.result, words.pc]
    simpa [destination, initialPC, mask] using link
  have directEven : input.instruction.indirect = false → input.base.lo % 2 = 0 ∧ input.offset.lo % 2 = 0 := by
    intro direct
    have aligned := codeAligned
    have initialEven : input.pc.lo % 2 = 0 := by
      rw [words.pc, canonical]
      dsimp [Word.ofBitVec, limbBase]
      omega
    cases kind : input.instruction
    · have parity := Reference.Sail.decoded_offset_even entry.bits initial entry.instruction initial source.decoded
      rw [encoding] at parity
      simp only [instruction, JumpBranchSlt.Jump.instruction, kind] at parity
      refine ⟨by simpa [JumpBranchSlt.Jump.Input.base, direct] using initialEven, ?_⟩
      rw [offset]
      simpa [metadata, kind] using Reference.Sail.sign_extend_low_even (by decide) _ parity
    · simp [kind, JumpBranchSlt.Jump.Instruction.indirect] at direct
  have baseBound : input.base.Bounded := by
    unfold JumpBranchSlt.Jump.Input.base
    split <;> assumption
  have modelCore := core
  rw [setupBinding] at modelCore
  have target := UnifiedReduced.Proofs.jump_pc hp input.instruction.indirect modelCore selected other binary noROM
    (base := input.base) (offset := input.offset) (final := output.pc)
    (by
      rw [words.offset, words.nextPC]
      refine ⟨?_, ?_, (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩
      all_goals cases mode : input.instruction.indirect
      all_goals simp [JumpBranchSlt.Jump.Input.base, mode, words.source,
        words.pc, sourceWord, initialPC])
    baseBound.1 (fun _ => baseBound.2) offsetBound directEven
    (by simpa [words.nextPC, finalPC] using (UnifiedReduced.Proofs.pc_bounds core).2)
  have extension : input.offset.toBitVec = match input.instruction with
      | .jal imm => SailRV32.Functions.sign_extend (m := 32) imm
      | .jalr imm => SailRV32.Functions.sign_extend (m := 32) imm := by
    rw [offset]; exact Word.ofBitVec_roundtrip _
  have csrs := sail_history_control_flow_csrs past
  simp [retiredState, Std.ExtDHashMap.get?_insert] at csrs
  have misaRead : ∃ value, run (SailRV32.readReg .misa) input.before = .ok value input.before := by
    obtain ⟨value, read⟩ := isa
    refine ⟨value, read_register ?_⟩
    simpa [retiredState, Std.ExtDHashMap.get?_insert] using csrs.1.trans read
  have landingPad : input.instruction.indirect = true →
      run (SailRV32.readReg .cur_privilege) input.before = .ok .Machine input.before ∧
      ∃ security, run (SailRV32.readReg .mseccfg) input.before = .ok security input.before ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0 := by
    intro indirect
    obtain ⟨privilege, security, securityRead, disabled⟩ := landingPad indirect
    constructor
    · apply read_register
      simpa [retiredState, Std.ExtDHashMap.get?_insert] using csrs.2.1.trans privilege
    · refine ⟨security, read_register ?_, disabled⟩
      simpa [retiredState, Std.ExtDHashMap.get?_insert] using csrs.2.2.trans securityRead
  exact retire_jump input output link target.1 target.2 extension sourceRead pcRead misaRead landingPad

theorem soundness_from_memory [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (inputs : NativeInputs projection trace initial cells program) (accepted : Accepted trace)
    (memory : MemoryExecution trace initial cells) (setup : trace.rom = Setup.table initial)
    {input : Input} {output : Output} {w : Nat → ZMod p}
    (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    (words : WordMapping input output w)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = instruction input)
    (codeAligned : entry.pc.toNat % 4 = 0)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (landingPad : input.instruction.indirect = true →
      initial.regs.get? .cur_privilege = some .Machine ∧
        ∃ security, initial.regs.get? .mseccfg = some security ∧
          SailRV32.Functions._get_Seccfg_MLPE security = 0)
    : JumpBranchSlt.Jump.spec input output := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  obtain ⟨events, after, past, history⟩ := UnifiedReduced.Proofs.row_position_from_memory clockSize inverse
    accepted inputs.clocks memory position
  have ranges := (UnifiedReduced.Proofs.value_bounds clockSize inverse accepted inputs.clocks inputs.image).1 _ member
  have leftRange := ranges importedConstraintsMemoryPorts[0]
    (by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before := by
    obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := position
    rw [state, words.pc]
    exact retired_state_pc middle _
  exact soundness_from_history hp core setup
    (by simpa [words.pc, Row.start, Row.columns, CircuitLayout.columns, PCState.State.word,
      rawPair, importedConstraintsTraceColumns, initialPC] using past) history leftRange words source query encoding codeAligned isa landingPad pcRead

theorem soundness [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) JumpBranchSlt.Jump.spec := by
  rintro input output w ⟨assumptions, ⟨accepted, decoded, member⟩, mapping⟩
  obtain ⟨addresses, image⟩ := assumptions.initialization.programImage
  obtain ⟨entry, present, query, encoding⟩ := mapping.instruction
  exact soundness_from_memory hp inverse assumptions.initialization accepted
    (UnifiedReduced.Proofs.memory_execution (by dsimp [timestampBase]; omega) inverse accepted assumptions.initialization decoded)
    assumptions.setup member mapping.words mapping.state (run_program_sources image entry present)
    query encoding (assumptions.codeAligned entry present) assumptions.isa assumptions.landingPad

end Airbender.UnifiedReduced.Jump.Proofs

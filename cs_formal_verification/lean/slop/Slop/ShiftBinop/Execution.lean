import Slop.ShiftBinop.Values
import Slop.ShiftBinop.PortReads
import Slop.Trace.Retirement

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

-- Constructor selection only; behavior is supplied by the original Sail clause.
def rowInstruction (operation : Operation) (immediate : Bool)
    (imm : BitVec 12) (rs1 rs2 rd : BitVec 5) : SailRV32.instruction :=
  match operation, immediate with
  | .rev8, _ => .REV8 (.Regidx rs1, .Regidx rd)
  | .xor, true => .ITYPE (imm, .Regidx rs1, .Regidx rd, .XORI)
  | .or, true => .ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI)
  | .and, true => .ITYPE (imm, .Regidx rs1, .Regidx rd, .ANDI)
  | .sll, true => .SHIFTIOP (imm.extractLsb' 0 6, .Regidx rs1, .Regidx rd, .SLLI)
  | .srl, true => .SHIFTIOP (imm.extractLsb' 0 6, .Regidx rs1, .Regidx rd, .SRLI)
  | .sra, true => .SHIFTIOP (imm.extractLsb' 0 6, .Regidx rs1, .Regidx rd, .SRAI)
  | .xor, false => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .XOR)
  | .or, false => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR)
  | .and, false => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND)
  | .sll, false => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLL)
  | .srl, false => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRL)
  | .sra, false => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRA)

def rowImmediate (operation : Operation) (immediate : Bool) (imm : BitVec 12) : Word :=
  if operation = .rev8 then ⟨0, 0⟩
  else if immediate then
    if operation.isShift then ⟨(imm.extractLsb' 0 6).toNat, 0⟩
    else binaryImmediate (SailRV32.Functions.sign_extend (m := 32) imm)
  else ⟨0, 0⟩

set_option maxHeartbeats 2000000 in
theorem row_decoder_shape {entry : ProgramEntry} (operation : Operation) (immediate : Bool)
    (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = rowInstruction operation immediate imm rs1 rs2 rd)
    (fields : decoderFields entry.instruction = some entry.data) :
    entry.data = ⟨(), rs1, if immediate || operation = .rev8 then 0 else rs2,
      rd, rowImmediate operation immediate imm,
      if operation.isShift then 1 else 2, operation.tag⟩ ∧
    (immediate = true → operation.isShift = true → operation ≠ .rev8 →
      (imm.extractLsb' 0 6).toNat < 32) := by
  rw [encoding] at fields
  cases operation <;> cases immediate
  all_goals simp [rowInstruction, decoderFields, instructionFields] at fields
  all_goals try split_ifs at fields
  all_goals simp_all [rowImmediate, Operation.isShift, Operation.tag]

set_option maxHeartbeats 2000000 in
/-- Register/immediate forms and REV8 retire into the actual native after-state.
    Reads, byte mappings, x0 preprocessing and PC bounds are derived. -/
theorem local_row_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (active : w 4 = 1) {initial : State} {cells : List Cell} (epoch : Nat)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (zeroReads : ∀ port ∈ importedConstraintsMemoryPorts,
      port.address.code w = (Cell.register 0).addressCode → (readToken w port).value = 0)
    (operation : Operation) (immediateForm : Bool) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = rowInstruction operation immediateForm imm rs1 rs2 rd)
    {before after : State}
    (history : Trace.SailHistory cells (nativeEvents epoch w).reverse before after) :
    let input : Input := ⟨operation, immediateForm,
      Trace.memoryWord (importedConstraintsMemoryPorts[0].readCode w),
      (if immediateForm && !operation.isShift then SailRV32.Functions.sign_extend (m := 32) imm
        else Trace.memoryWord (importedConstraintsMemoryPorts[1].readCode w)),
      ⟨(w 0).val, (w 1).val⟩, .Regidx rs1,
      .Regidx (if immediateForm || operation = .rev8 then 0 else rs2), .Regidx rd, imm,
      Trace.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec⟩
    run (normalStep (execution input)) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (Trace.retiredState after (⟨(w 13).val, (w 14).val⟩ : Word).toBitVec) := by
  let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
  let rebased := Trace.retiredState before currentPC
  let finished := Trace.retiredState after currentPC
  have history' := Trace.Proofs.retired_state_history history currentPC
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  let data : DecoderData Unit := ⟨(), rs1, if immediateForm || operation = .rev8 then 0 else rs2,
    rd, rowImmediate operation immediateForm imm,
    if operation.isShift then 1 else 2, operation.tag⟩
  obtain ⟨shape, legalShift⟩ := row_decoder_shape operation immediateForm imm rs1 rs2 rd encoding source.fields
  change entry.data = data at shape
  have flags := decoder_selectors limbField h (decoder_field_bounds source.fields).2.1 query
  have selected : if operation.isShift then w 11 = 1 ∧ w 12 = 0 else w 11 = 0 ∧ w 12 = 1 := by
    have a := flags 0
    have b := flags 1
    cases operation
    all_goals simp only [Operation.isShift, ite_true]
    all_goals constructor
    all_goals first
      | (simpa [shape, data, Operation.isShift, importedConstraintsDecoderColumns, Nat.testBit] using a)
      | (simpa [shape, data, Operation.isShift, importedConstraintsDecoderColumns, Nat.testBit] using b)
  have funct3 := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
  change w 10 = (entry.data.funct3 : ZMod p) at funct3
  rw [shape] at funct3
  have immediate : w 8 = (data.immediate.lo : ZMod p) ∧ w 9 = (data.immediate.hi : ZMod p) := by
    have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
    have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
    change w 8 = (entry.data.immediate.lo : ZMod p) at low
    change w 9 = (entry.data.immediate.hi : ZMod p) at high
    rw [shape] at low high
    constructor
    · simpa [data] using low
    · simpa [data] using high
  have indices := Trace.Proofs.native_query_indices limbField query
  have leftIndex : w 5 = (rs1.toNat : ZMod p) := by
    have index := indices.1
    change (w 5).val = entry.data.rs1.toNat at index
    rw [shape] at index
    exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have rightIndex : w 6 = ((if immediateForm || operation = .rev8 then 0 else rs2).toNat : ZMod p) := by
    have index := indices.2.1
    change (w 6).val = entry.data.rs2.toNat at index
    rw [shape] at index
    exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have rdIndex : w 7 = (rd.toNat : ZMod p) := by
    have index := indices.2.2
    change (w 7).val = entry.data.rd.toNat at index
    rw [shape] at index
    exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have zeroRead : immediateForm || operation = .rev8 → importedConstraintsMemoryPorts[1].readCode w = 0 := by
    intro zero
    have atZero := register_addresses limbField query 1
    simp [shape, data, zero] at atZero
    exact zeroReads _ (by simp [importedConstraintsMemoryPorts]) atZero
  let input : Input := ⟨operation, immediateForm,
    Trace.memoryWord (importedConstraintsMemoryPorts[0].readCode w),
    (if immediateForm && !operation.isShift then SailRV32.Functions.sign_extend (m := 32) imm
        else Trace.memoryWord (importedConstraintsMemoryPorts[1].readCode w)),
    ⟨(w 0).val, (w 1).val⟩, .Regidx rs1, .Regidx (if immediateForm || operation = .rev8 then 0 else rs2),
    .Regidx rd, imm, rebased⟩
  let output : Output := ⟨⟨(w 31).val, (w 32).val⟩, ⟨(w 13).val, (w 14).val⟩⟩
  have binaryTags : operation.isShift = false → operation.tag = 4 ∨ operation.tag = 6 ∨ operation.tag = 7 := by
    cases operation <;> simp [Operation.isShift, Operation.tag]
  have mapping : RowWordMapping input output w := by
    constructor
    · cases shift : operation.isShift
      · exact binary_left_bytes (by omega) h (by simpa [shift] using selected)
          operation.tag (binaryTags shift) funct3
      · exact shift_left_bytes (by omega) h (by simpa [shift] using selected)
    · intro binary
      change operation.isShift = false at binary
      cases form : immediateForm
      · have plain : w 8 = 0 ∧ w 9 = 0 := by
          simpa [data, rowImmediate, form, binary,
            show operation ≠ .rev8 by intro e; simp [e, Operation.isShift] at binary] using immediate
        simpa [input, form] using binary_register_right_bytes (by omega) h
          (by simpa [binary] using selected) operation.tag (binaryTags binary) funct3 plain
      · have packed : w 8 = ((SailRV32.Functions.sign_extend (m := 32) imm).extractLsb' 0 8).toNat ∧
            w 9 = ((SailRV32.Functions.sign_extend (m := 32) imm).extractLsb' 8 8).toNat := by
          simpa [data, rowImmediate, form, binary, binaryImmediate, BitVec.extractLsb'_toNat,
            Nat.shiftRight_eq_div_pow, show operation ≠ .rev8 by intro e; simp [e, Operation.isShift] at binary] using immediate
        simpa [input, form, binary] using binary_immediate_right_bytes (by omega) h
          (by simpa [binary] using selected) operation.tag (binaryTags binary) funct3 imm packed
          (by simpa only [show Nat.pair 0 0 = 0 by decide] using zeroRead (by simp [form]))
    · intro shift
      change operation.isShift = true at shift
      have byte := shift_right_low_byte (by omega) h (by simpa [shift] using selected)
      by_cases zero : immediateForm || operation = .rev8
      · rw [zeroRead zero] at byte
        simpa [input, zero, shift, show Trace.memoryWord 0 = (0 : BitVec 32) by decide] using byte
      · simpa [input, zero, shift] using byte
    · intro shift
      change operation.isShift = true at shift
      by_cases reverse : operation = .rev8
      · simpa [input, data, rowImmediate, reverse] using immediate.1
      · cases form : immediateForm
        · simpa [input, data, rowImmediate, reverse, form] using immediate.1
        · have legal := legalShift form shift reverse
          have low : (imm.extractLsb' 0 6).toNat = (imm.extractLsb' 0 5).toNat := by
            simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] at legal ⊢
            norm_num at legal ⊢
            omega
          simpa [input, data, rowImmediate, reverse, form, shift, low] using immediate.1
    · exact leftIndex
    · exact rightIndex
    · exact rdIndex
    · exact (ZMod.natCast_zmod_val _).symm
    · exact (ZMod.natCast_zmod_val _).symm
    all_goals rfl
  have readLeft := register_reads limbField epoch query history' ⟨0, by decide⟩
  have readRight := register_reads limbField epoch query history' ⟨1, by decide⟩
  have interface : RowInterfaces input output w := by
    constructor
    · exact active
    · exact selected
    · exact funct3
    · have nonzero := decoder_nonzero_destination source.fields
      rw [shape] at nonzero
      intro equality
      exact nonzero (SailRV32.regidx.Regidx.inj equality)
    · have pc := Trace.Proofs.native_query_pc_word limbField query
      have bound : (Word.mk (w 0).val (w 1).val).Bounded :=
        pc.symm ▸ Word.ofBitVec_bound entry.pc
      exact bound
    · simpa [shape, data, input] using readLeft
    · intro form nonreverse
      change immediateForm = false at form
      change operation ≠ .rev8 at nonreverse
      simpa [shape, data, input, form, nonreverse] using readRight
    · intro form binary
      change immediateForm = true at form
      change operation.isShift = false at binary
      simp [input, form, binary]
    · exact legalShift
    · exact Trace.Proofs.retired_state_pc before currentPC
  obtain ⟨checkedAfter, normal, projected⟩ := soundness (by omega) inverse input output w ⟨interface, h, mapping⟩
  have written := register_write limbField epoch query history'
  have write : run (SailRV32.Functions.wX_bits (.Regidx rd) output.destination.toBitVec) rebased =
      .ok () finished := by
    simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.writeCode,
      WordColumns.code, WordColumns.evaluate, Trace.memoryWord, Nat.unpair_pair, output] using written
  have nativeProjection := Trace.Proofs.projected_step_of_write rd output write
  have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
  rw [same] at normal
  simpa only [input, output, rebased, finished, currentPC, Trace.Proofs.retired_state_overwrite] using normal

/-- Family-only compatibility entry; the local proof also serves pooled histories. -/
theorem row_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : ShiftBinop.programImage initial addresses = some program)
    (decoded : Decoded trace program)
    {w : Nat → ZMod p} (member : (⟨.shiftBinop, w⟩ : Row p TraceKind) ∈ trace.rows)
    {entry : ProgramEntry} (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (operation : Operation) (immediateForm : Bool) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = rowInstruction operation immediateForm imm rs1 rs2 rd)
    {before after : State}
    (history : Trace.SailHistory cells (nativeEvents trace.memoryEpoch w).reverse before after)
    (configuration : Reference.RiscV.Sail.Configured initial := by find_configured) :
    let input : Input := ⟨operation, immediateForm,
      Trace.memoryWord (importedConstraintsMemoryPorts[0].readCode w),
      (if immediateForm && !operation.isShift then SailRV32.Functions.sign_extend (m := 32) imm
        else Trace.memoryWord (importedConstraintsMemoryPorts[1].readCode w)),
      ⟨(w 0).val, (w 1).val⟩, .Regidx rs1,
      .Regidx (if immediateForm || operation = .rev8 then 0 else rs2), .Regidx rd, imm,
      Trace.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec⟩
    run (normalStep (execution input)) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (Trace.retiredState after (⟨(w 13).val, (w 14).val⟩ : Word).toBitVec) := by
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have zeros : ∀ port ∈ importedConstraintsMemoryPorts,
      port.address.code w = (Cell.register 0).addressCode → (readToken w port).value = 0 := by
    intro port present atZero
    exact (native_zero_reads clockField clockInverse accepted clocks image programImage decoded)
      _ member port (by simpa [Row.ports] using present) atZero
  exact local_row_execution hp inverse h (accepted.active _ member) trace.memoryEpoch
    (Trace.Proofs.run_program_sources programImage entry present) query zeros
    operation immediateForm imm rs1 rs2 rd encoding history

end Airbender.ShiftBinop.Proofs

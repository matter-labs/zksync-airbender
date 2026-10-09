import Airbender.Proofs.ShiftBinop.Values
import Airbender.Proofs.ShiftBinop.PortReads
import Airbender.Proofs.Trace.Retirement

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

-- Constructor selection only; behavior is supplied by the original Sail clause.
def registerInstruction (operation : Operation) (rs1 rs2 rd : BitVec 5) : SailRV32.instruction :=
  match operation with
  | .xor => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .XOR)
  | .or => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR)
  | .and => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND)
  | .sll => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLL)
  | .srl => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRL)
  | .sra => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRA)
  | .rev8 => .REV8 (.Regidx rs1, .Regidx rd)

set_option maxHeartbeats 2000000 in
/-- All register forms and REV8 retire into the actual native after-state.
    Reads, byte mappings, x0 preprocessing and PC bounds are derived. -/
theorem register_row_execution {p : Nat} [Fact p.Prime]
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
    (operation : Operation) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = registerInstruction operation rs1 rs2 rd)
    {before after : State}
    (history : Trace.Proofs.SailHistory cells (nativeEvents trace.memoryEpoch w).reverse before after) :
    let input : Input := ⟨operation, false,
      Trace.Proofs.memoryWord (importedConstraintsMemoryPorts[0].readCode w),
      Trace.Proofs.memoryWord (importedConstraintsMemoryPorts[1].readCode w),
      ⟨(w 0).val, (w 1).val⟩, .Regidx rs1,
      .Regidx (if operation = .rev8 then 0 else rs2), .Regidx rd, 0,
      Trace.Proofs.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec⟩
    run (normalStep (execution input)) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (Trace.Proofs.retiredState after (⟨(w 13).val, (w 14).val⟩ : Word).toBitVec) := by
  let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
  let rebased := Trace.Proofs.retiredState before currentPC
  let finished := Trace.Proofs.retiredState after currentPC
  have history' := Trace.Proofs.retired_state_history history currentPC
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have source := Trace.Proofs.run_program_sources programImage entry present
  let data : DecoderData Unit := ⟨(), rs1, if operation = .rev8 then 0 else rs2, rd, ⟨0, 0⟩,
    if operation.isShift then 1 else 2, operation.tag⟩
  have shape : entry.data = data := by
    have fields := source.fields
    rw [encoding] at fields
    cases operation <;> simp [registerInstruction, decoderFields, instructionFields] at fields
    all_goals exact fields.2.symm
  have flags := decoder_selectors limbField h (decoder_field_bounds source.fields).2.1 query
  have selected : if operation.isShift then w 11 = 1 ∧ w 12 = 0 else w 11 = 0 ∧ w 12 = 1 := by
    have a := flags 0
    have b := flags 1
    cases operation
    all_goals simp only [Operation.isShift, if_true]
    all_goals constructor
    all_goals first
      | (simpa [shape, data, Operation.isShift, importedConstraintsDecoderColumns, Nat.testBit] using a)
      | (simpa [shape, data, Operation.isShift, importedConstraintsDecoderColumns, Nat.testBit] using b)
  have funct3 := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
  change w 10 = (entry.data.funct3 : ZMod p) at funct3
  rw [shape] at funct3
  have immediate : w 8 = 0 ∧ w 9 = 0 := by
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
  have rightIndex : w 6 = ((if operation = .rev8 then 0 else rs2).toNat : ZMod p) := by
    have index := indices.2.1
    change (w 6).val = entry.data.rs2.toNat at index
    rw [shape] at index
    exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have rdIndex : w 7 = (rd.toNat : ZMod p) := by
    have index := indices.2.2
    change (w 7).val = entry.data.rd.toNat at index
    rw [shape] at index
    exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have zeroRead : operation = .rev8 → importedConstraintsMemoryPorts[1].readCode w = 0 := by
    intro reverse
    have atZero := register_addresses limbField query 1
    simp [shape, data, reverse] at atZero
    exact native_zero_reads clockField clockInverse accepted clocks image programImage decoded
      _ member _ (by simp [Row.ports, importedConstraintsMemoryPorts]) atZero
  let input : Input := ⟨operation, false,
    Trace.Proofs.memoryWord (importedConstraintsMemoryPorts[0].readCode w),
    Trace.Proofs.memoryWord (importedConstraintsMemoryPorts[1].readCode w),
    ⟨(w 0).val, (w 1).val⟩, .Regidx rs1, .Regidx (if operation = .rev8 then 0 else rs2),
    .Regidx rd, 0, rebased⟩
  let output : Output := ⟨⟨(w 31).val, (w 32).val⟩, ⟨(w 13).val, (w 14).val⟩⟩
  have binaryTags : operation.isShift = false → operation.tag = 4 ∨ operation.tag = 6 ∨ operation.tag = 7 := by
    cases operation <;> simp [Operation.isShift, Operation.tag]
  have mapping : WordMapping input output w := by
    constructor
    · cases shift : operation.isShift
      · exact binary_left_bytes (by omega) h (by simpa [shift] using selected)
          operation.tag (binaryTags shift) funct3
      · exact shift_left_bytes (by omega) h (by simpa [shift] using selected)
    · intro binary
      exact binary_register_right_bytes (by omega) h (by simpa [input, binary] using selected)
        operation.tag (binaryTags binary) funct3 immediate
    · intro shift
      have byte := shift_right_low_byte (by omega) h (by simpa [input, shift] using selected)
      by_cases reverse : operation = .rev8
      · rw [zeroRead reverse] at byte
        simpa [input, reverse, show Trace.Proofs.memoryWord 0 = (0 : BitVec 32) by decide] using byte
      · simpa [input, reverse] using byte
    · intro shift
      simpa [input] using immediate.1
    · exact leftIndex
    · exact rightIndex
    · exact rdIndex
    · exact (ZMod.natCast_zmod_val _).symm
    · exact (ZMod.natCast_zmod_val _).symm
    all_goals rfl
  have readLeft := register_reads limbField trace.memoryEpoch query history' ⟨0, by decide⟩
  have readRight := register_reads limbField trace.memoryEpoch query history' ⟨1, by decide⟩
  have interface : InterfaceAssumptions input output w := by
    constructor
    · exact accepted.active _ member
    · exact selected
    · exact funct3
    · have nonzero := decoder_nonzero_destination source.fields
      rw [shape] at nonzero
      intro equality
      exact nonzero (SailRV32.regidx.Regidx.inj equality)
    · exact incoming_pc_bounds limbField decoded _ member
    · simpa [shape, data, input] using readLeft
    · intro immediate nonreverse
      simpa [shape, data, input] using readRight
    · simp [input]
    · simp [input]
    · exact Trace.Proofs.retired_state_pc before currentPC
  obtain ⟨checkedAfter, normal, projected⟩ := soundness (by omega) inverse input output w ⟨interface, h, mapping⟩
  have written := register_write limbField trace.memoryEpoch query history'
  have write : run (SailRV32.Functions.wX_bits (.Regidx rd) output.destination.toBitVec) rebased =
      .ok () finished := by
    simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.writeCode,
      WordColumns.code, WordColumns.evaluate, Trace.Proofs.memoryWord, Nat.unpair_pair, output] using written
  have nativeProjection := Trace.Proofs.projected_step_of_write rd output write
  have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
  rw [same] at normal
  simpa only [input, output, rebased, finished, currentPC, Trace.Proofs.retired_state_overwrite] using normal

end Airbender.ShiftBinop.Proofs

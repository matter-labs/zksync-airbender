import Airbender.Proofs.MulDiv.Values
import Airbender.Proofs.MulDiv.PortReads
import Airbender.Proofs.MulDiv.Soundness
import Airbender.Proofs.Trace.Retirement

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

set_option maxHeartbeats 2000000 in
/-- All four clauses reach the actual native row after-state. Selectors, input
    bounds and register reads are derived from public decoding and history. -/
theorem local_row_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    {initial : State} {cells : List Cell} (epoch : Nat)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (leftBound : (Word.mk (w 20).val (w 21).val).Bounded)
    (operation : Operation) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = match operation with
      | .mul => .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.Low, .Signed, .Signed⟩)
      | .mulhu => .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.High, .Unsigned, .Unsigned⟩)
      | .divu => .DIV (.Regidx rs2, .Regidx rs1, .Regidx rd, true)
      | .remu => .REM (.Regidx rs2, .Regidx rs1, .Regidx rd, true))
    {before after : State}
    (history : Trace.Proofs.SailHistory cells (nativeEvents epoch w).reverse before after) :
    let input : Input := ⟨operation, ⟨(w 20).val, (w 21).val⟩, ⟨(w 24).val, (w 25).val⟩,
      ⟨(w 0).val, (w 1).val⟩, .Regidx rs1, .Regidx rs2, .Regidx rd,
      Trace.Proofs.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec⟩
    run (normalStep (execution input)) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (Trace.Proofs.retiredState after (⟨(w 14).val, (w 15).val⟩ : Word).toBitVec) := by
  let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
  let rebased := Trace.Proofs.retiredState before currentPC
  let finished := Trace.Proofs.retiredState after currentPC
  have history' := Trace.Proofs.retired_state_history history currentPC
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  let data : DecoderData Unit := ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 2 ^ operation.selector.val, 0⟩
  have shape : entry.data = data := by
    have fields := source.fields
    rw [encoding] at fields
    cases operation <;> simp [decoderFields] at fields <;> exact fields.2.symm
  have flags := decoder_selectors limbField h (decoder_field_bounds source.fields).2.1 query
  have selected : ∀ i : Fin 4, w (10 + i.val) = if i = operation.selector then 1 else 0 := by
    intro i
    have bit := flags i
    cases operation <;> fin_cases i <;>
      simpa [shape, data, Operation.selector, importedConstraintsDecoderColumns, Nat.testBit] using bit
  have pcBound : (Word.mk (w 0).val (w 1).val).Bounded := by
    have pc := Trace.Proofs.native_query_pc_word limbField query
    exact pc.symm ▸ Word.ofBitVec_bound entry.pc
  have indices := Trace.Proofs.native_query_indices limbField query
  have leftIndex : w 5 = (rs1.toNat : ZMod p) := by
    have index := indices.1
    change (w 5).val = entry.data.rs1.toNat at index
    rw [shape] at index
    exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have rightIndex : w 6 = (rs2.toNat : ZMod p) := by
    have index := indices.2.1
    change (w 6).val = entry.data.rs2.toNat at index
    rw [shape] at index
    exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have rdIndex : w 7 = (rd.toNat : ZMod p) := by
    have index := indices.2.2
    change (w 7).val = entry.data.rd.toNat at index
    rw [shape] at index
    exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  let input : Input := ⟨operation, ⟨(w 20).val, (w 21).val⟩, ⟨(w 24).val, (w 25).val⟩,
    ⟨(w 0).val, (w 1).val⟩, .Regidx rs1, .Regidx rs2, .Regidx rd, rebased⟩
  let output : Output := ⟨⟨(w 28).val, (w 29).val⟩, ⟨(w 14).val, (w 15).val⟩⟩
  have mapping : RowWordMapping input output w := by
    constructor <;> first | rfl | exact leftIndex | exact rightIndex | exact rdIndex |
      exact (ZMod.natCast_zmod_val _).symm
  have readLeft := register_reads limbField epoch query history' ⟨0, by decide⟩
  have readRight := register_reads limbField epoch query history' ⟨1, by decide⟩
  have interface : RowInterfaces input output w := by
    constructor
    · exact selected
    · exact leftBound
    · exact pcBound
    · simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.readCode,
        pairCode, Trace.Proofs.memoryWord, input] using readLeft
    · simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.readCode,
        pairCode, Trace.Proofs.memoryWord, input] using readRight
    · exact Trace.Proofs.retired_state_pc before currentPC
  obtain ⟨checkedAfter, normal, projected⟩ := soundness hp inverse input output w ⟨interface, h, mapping⟩
  have written := register_write limbField epoch query history'
  have write : run (SailRV32.Functions.wX_bits (.Regidx rd) output.destination.toBitVec) rebased =
      .ok () finished := by
    simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.writeCode,
      pairCode, Trace.Proofs.memoryWord, output] using written
  have nativeProjection := Trace.Proofs.projected_step_of_write rd output write
  have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
  rw [same] at normal
  simpa only [input, output, rebased, finished, currentPC,
    Trace.Proofs.retired_state_overwrite] using normal

/-- Family-only compatibility entry; the local proof also serves pooled histories. -/
theorem row_rebased_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : MulDiv.programImage initial addresses = some program)
    (_decoded : Decoded trace program)
    {w : Nat → ZMod p} (member : (⟨.mulDiv, w⟩ : Row p TraceKind) ∈ trace.rows)
    {entry : ProgramEntry} (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (operation : Operation) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = match operation with
      | .mul => .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.Low, .Signed, .Signed⟩)
      | .mulhu => .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.High, .Unsigned, .Unsigned⟩)
      | .divu => .DIV (.Regidx rs2, .Regidx rs1, .Regidx rd, true)
      | .remu => .REM (.Regidx rs2, .Regidx rs1, .Regidx rd, true))
    {before after : State}
    (history : Trace.Proofs.SailHistory cells (nativeEvents trace.memoryEpoch w).reverse before after) :
    let input : Input := ⟨operation, ⟨(w 20).val, (w 21).val⟩, ⟨(w 24).val, (w 25).val⟩,
      ⟨(w 0).val, (w 1).val⟩, .Regidx rs1, .Regidx rs2, .Regidx rd,
      Trace.Proofs.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec⟩
    run (normalStep (execution input)) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (Trace.Proofs.retiredState after (⟨(w 14).val, (w 15).val⟩ : Word).toBitVec) := by
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have bound := (native_value_bounds clockField clockInverse accepted clocks image).1
    _ member importedConstraintsMemoryPorts[0] (by simp [Row.ports, importedConstraintsMemoryPorts])
  have left : (Word.mk (w 20).val (w 21).val).Bounded := by
    simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts] using bound
  exact local_row_execution hp inverse h trace.memoryEpoch
    (Trace.Proofs.run_program_sources programImage entry present) query left operation rs1 rs2 rd encoding history

end Airbender.MulDiv.Proofs

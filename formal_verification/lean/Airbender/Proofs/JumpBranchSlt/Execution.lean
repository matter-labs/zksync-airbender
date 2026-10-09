import Airbender.Proofs.JumpBranchSlt.Values
import Airbender.Proofs.JumpBranchSlt.PortReads
import Airbender.Proofs.JumpBranchSlt.JumpSoundness
import Airbender.Proofs.Trace.Retirement

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

set_option maxHeartbeats 2000000 in
/-- An actual public-decoded JALR row executes Sail's original clause and
    retirement. Register ranges/reads, selectors and PC reads are derived.
    Canonical termination and Machine/MLPE configuration remain boundaries. -/
theorem jalr_rebased_step {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : JumpBranchSlt.programImage initial addresses = some program)
    (decoded : Decoded trace program) (terminal : trace.terminal.word.Bounded)
    {w : Nat → ZMod p} (member : (⟨.jumpBranchSlt, w⟩ : Row p TraceKind) ∈ trace.rows)
    {entry : ProgramEntry} (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (imm : BitVec 12) (rs1 rd : BitVec 5)
    (encoding : entry.instruction = .JALR (imm, .Regidx rs1, .Regidx rd))
    {before after : State}
    (history : Trace.Proofs.SailHistory cells (nativeEvents trace.memoryEpoch w).reverse before after)
    (isa : ∃ value, before.regs.get? .misa = some value)
    (privilege : before.regs.get? .cur_privilege = some .Machine)
    {security : BitVec 64} (securityRead : before.regs.get? .mseccfg = some security)
    (landingPad : SailRV32.Functions._get_Seccfg_MLPE security = 0) :
    let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
    let finalPC := (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec
    run (normalStep (SailRV32.Functions.execute_JALR imm (.Regidx rs1) (.Regidx rd)))
      (Trace.Proofs.retiredState before currentPC) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (Trace.Proofs.retiredState after finalPC) := by
  let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
  let finalPC := (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec
  let rebased := Trace.Proofs.retiredState before currentPC
  let finished := Trace.Proofs.retiredState after currentPC
  have history' := Trace.Proofs.retired_state_history history currentPC
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have source := Trace.Proofs.program_sources programImage entry present
  let data : DecoderData Unit := ⟨(), rs1, 0, rd,
    Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), if rd = 0 then 18 else 2, 0⟩
  have shape : entry.data = data := by
    have fields := source.fields
    rw [encoding] at fields
    simp only [decoderFields, Option.some.injEq] at fields
    exact fields.symm
  have fields := decoder_field_bounds source.fields
  have flags := decoder_selectors limbField h fields.2.1 query
  have f0 := flags ⟨0, by decide⟩
  have f1 := flags ⟨1, by decide⟩
  have f2 := flags ⟨2, by decide⟩
  have f3 := flags ⟨3, by decide⟩
  have f4 := flags ⟨4, by decide⟩
  have selectors : w 11 = 0 ∧ w 12 = 1 ∧ w 13 = 0 ∧ w 14 = 0 ∧
      w 15 = if rd = 0 then 1 else 0 := by
    by_cases zero : rd = 0
    all_goals simp_all [importedConstraintsDecoderColumns, data, Nat.testBit]
  have sourceBound := (native_value_bounds hp inverse accepted clocks image programImage decoded).1
    _ member importedConstraintsMemoryPorts[0] (by simp [Row.ports, importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at sourceBound
  change (⟨(w 22).val, (w 23).val⟩ : Word).Bounded at sourceBound
  have pcBounds := trace_pc_bounds limbField accepted decoded terminal _ member
  have indices := Trace.Proofs.native_query_indices limbField query
  have leftIndex : w 5 = (rs1.toNat : ZMod p) := by
    have index := indices.1
    change (w 5).val = entry.data.rs1.toNat at index
    rw [shape] at index
    calc
      w 5 = ((w 5).val : ZMod p) := (ZMod.natCast_zmod_val _).symm
      _ = (rs1.toNat : ZMod p) := by rw [index]
  have rdIndex : w 7 = (rd.toNat : ZMod p) := by
    have index := indices.2.2
    change (w 7).val = entry.data.rd.toNat at index
    rw [shape] at index
    calc
      w 7 = ((w 7).val : ZMod p) := (ZMod.natCast_zmod_val _).symm
      _ = (rd.toNat : ZMod p) := by rw [index]
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
  change w 8 = (entry.data.immediate.lo : ZMod p) at low
  change w 9 = (entry.data.immediate.hi : ZMod p) at high
  let input : Jump.Input := ⟨.jalr imm, ⟨(w 22).val, (w 23).val⟩,
    entry.data.immediate, ⟨(w 0).val, (w 1).val⟩, .Regidx rs1, .Regidx rd, rebased⟩
  let output : Output := ⟨⟨(w 30).val, (w 31).val⟩, ⟨(w 16).val, (w 17).val⟩⟩
  have mapping : Jump.WordMapping input output w := by
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, low, high, rfl, rfl⟩,
      ⟨rfl, rfl⟩, fun _ => leftIndex, rdIndex⟩
  have read := register_reads limbField trace.memoryEpoch query history' ⟨0, by decide⟩
  have sourceRead : run (SailRV32.Functions.rX_bits (.Regidx rs1)) rebased =
      .ok input.source.toBitVec rebased := by
    simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.readCode,
      pairCode, Trace.Proofs.memoryWord, input] using read
  have interface : Jump.InterfaceAssumptions input output w := by
    constructor
    · exact accepted.active _ member
    · exact ⟨selectors.1, selectors.2.1⟩
    · exact ⟨selectors.2.2.1, selectors.2.2.2.1⟩
    · change w 15 = 1 ↔ .Regidx rd = zeroRegister
      rw [selectors.2.2.2.2]
      by_cases zero : rd = 0 <;> simp [zero, zeroRegister]
    · exact pcBounds.1.1
    · exact sourceBound.1
    · exact fun _ => sourceBound.2
    · exact fields.1
    · intro impossible; cases impossible
    · exact pcBounds.2.2
    · change entry.data.immediate.toBitVec = _
      rw [shape]
      exact Word.ofBitVec_roundtrip _
    · exact fun _ => sourceRead
    · exact Trace.Proofs.retired_state_pc before currentPC
    · obtain ⟨value, read⟩ := isa
      refine ⟨value, read_register ?_⟩
      simpa [input, rebased, Trace.Proofs.retiredState, Std.ExtDHashMap.get?_insert] using read
    · intro _
      constructor
      · apply read_register
        simpa [input, rebased, Trace.Proofs.retiredState, Std.ExtDHashMap.get?_insert] using privilege
      · refine ⟨security, read_register ?_, landingPad⟩
        simpa [input, rebased, Trace.Proofs.retiredState, Std.ExtDHashMap.get?_insert] using securityRead
  obtain ⟨checkedAfter, normal, projected⟩ := jump_soundness hp input output w
    ⟨interface, h, mapping⟩
  have written := register_write limbField trace.memoryEpoch query history'
  have write : run (SailRV32.Functions.wX_bits (.Regidx rd) output.destination.toBitVec) rebased =
      .ok () finished := by
    simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.writeCode,
      pairCode, Trace.Proofs.memoryWord, output] using written
  have nativeProjection := Trace.Proofs.projected_step_of_write rd output write
  have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
  rw [same] at normal
  simpa only [Jump.execution, input, output, rebased, finished,
    Trace.Proofs.retired_state_overwrite] using normal

end Airbender.JumpBranchSlt.Proofs

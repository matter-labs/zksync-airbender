import Airbender.Proofs.JumpBranchSlt.Values
import Airbender.Proofs.JumpBranchSlt.PortReads
import Airbender.Proofs.JumpBranchSlt.BranchSoundness
import Airbender.Proofs.Trace.Retirement

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Actual public decoding and native histories discharge every local branch
    interface. Sail determines the branch decision; the checked PC equations
    establish its retirement into the actual native after-state. -/
theorem branch_rebased_step {p : Nat} [Fact p.Prime]
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
    (opcode : SailRV32.bop) (imm : BitVec 13) (rs1 rs2 : BitVec 5)
    (encoding : entry.instruction = .BTYPE (imm, .Regidx rs2, .Regidx rs1, opcode))
    {before after : State} {events : List MemoryAccess}
    (history : Trace.Proofs.SailHistory cells (nativeEvents trace.memoryEpoch w).reverse before after)
    (past : Trace.Proofs.SailHistory cells events initial before)
    (isa : ∃ value, initial.regs.get? .misa = some value) :
    let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
    let finalPC := (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec
    run (normalStep (SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode))
      (Trace.Proofs.retiredState before currentPC) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (Trace.Proofs.retiredState after finalPC) := by
  let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
  let rebased := Trace.Proofs.retiredState before currentPC
  let finished := Trace.Proofs.retiredState after currentPC
  have history' := Trace.Proofs.retired_state_history history currentPC
  have csrs := Trace.Proofs.sail_history_control_flow_csrs past
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have source := Trace.Proofs.program_sources programImage entry present
  let data : DecoderData Unit := ⟨(), rs1, rs2, 0,
    Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 24, Branch.funct3 opcode⟩
  have shape : entry.data = data := by
    have fields := source.fields
    rw [encoding] at fields
    exact (Option.some.inj fields).symm
  have fields := decoder_field_bounds source.fields
  have flags := decoder_selectors limbField h fields.2.1 query
  have f0 := flags ⟨0, by decide⟩
  have f1 := flags ⟨1, by decide⟩
  have f2 := flags ⟨2, by decide⟩
  have f3 := flags ⟨3, by decide⟩
  have f4 := flags ⟨4, by decide⟩
  have selectors : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 0 ∧ w 14 = 1 ∧ w 15 = 1 := by
    simp_all [importedConstraintsDecoderColumns, data, Nat.testBit]
  have bounds := (native_value_bounds hp inverse accepted clocks image programImage decoded).1 _ member
  have leftBound := bounds importedConstraintsMemoryPorts[0]
    (by simp [Row.ports, importedConstraintsMemoryPorts])
  have rightBound := bounds importedConstraintsMemoryPorts[1]
    (by simp [Row.ports, importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at leftBound rightBound
  change (⟨(w 22).val, (w 23).val⟩ : Word).Bounded at leftBound
  change (⟨(w 26).val, (w 27).val⟩ : Word).Bounded at rightBound
  have pcBounds := trace_pc_bounds limbField accepted decoded terminal _ member
  have aligned := (trace_pc_alignment hp accepted initialAligned).1 _ member
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
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
  have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
  change w 8 = (entry.data.immediate.lo : ZMod p) at low
  change w 9 = (entry.data.immediate.hi : ZMod p) at high
  change w 10 = (entry.data.funct3 : ZMod p) at tag
  let input : Branch.Input := ⟨opcode, ⟨(w 22).val, (w 23).val⟩,
    ⟨(w 26).val, (w 27).val⟩, entry.data.immediate,
    ⟨(w 0).val, (w 1).val⟩, .Regidx rs1, .Regidx rs2, imm, rebased⟩
  let output : Output := ⟨⟨(w 30).val, (w 31).val⟩, ⟨(w 16).val, (w 17).val⟩⟩
  have mapping : Branch.WordMapping input output w := by
    constructor
    · exact ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩
    · exact ⟨rfl, rfl, low, high, rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact leftIndex
    · exact rightIndex
  have readLeft := register_reads limbField trace.memoryEpoch query history' ⟨0, by decide⟩
  have readRight := register_reads limbField trace.memoryEpoch query history' ⟨1, by decide⟩
  have interface : Branch.InterfaceAssumptions input output w := by
    constructor
    · exact accepted.active _ member
    · exact selectors.2.2.2.1
    · exact ⟨selectors.1, selectors.2.1, selectors.2.2.1⟩
    · simpa [shape, data] using tag
    · exact selectors.2.2.2.2
    · exact leftBound
    · exact rightBound
    · exact fields.1
    · exact pcBounds.1.1
    · exact aligned.1
    · simpa [encoding] using decoder_offset_even source
    · exact pcBounds.2.2
    · change entry.data.immediate.toBitVec = _
      rw [shape]
      exact Word.ofBitVec_roundtrip _
    · simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.readCode,
        pairCode, Trace.Proofs.memoryWord, input] using readLeft
    · simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.readCode,
        pairCode, Trace.Proofs.memoryWord, input] using readRight
    · exact Trace.Proofs.retired_state_pc before currentPC
    · obtain ⟨value, read⟩ := isa
      refine ⟨value, read_register ?_⟩
      simpa [input, rebased, Trace.Proofs.retiredState, Std.ExtDHashMap.get?_insert] using csrs.1.trans read
  obtain ⟨checkedAfter, normal, projected⟩ := branch_soundness hp input output w
    ⟨interface, h, mapping⟩
  have written := register_write limbField trace.memoryEpoch query history'
  have write : run (SailRV32.Functions.wX_bits (.Regidx 0) output.destination.toBitVec) rebased =
      .ok () finished := by
    simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.writeCode,
      pairCode, Trace.Proofs.memoryWord, output] using written
  have nativeProjection := Trace.Proofs.projected_step_of_write 0 output write
  have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
  rw [same] at normal
  simpa only [Branch.execution, input, output, rebased, finished,
    Trace.Proofs.retired_state_overwrite] using normal

end Airbender.JumpBranchSlt.Proofs

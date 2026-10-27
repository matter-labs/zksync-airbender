import Slop.JumpBranchSlt.Values
import Slop.JumpBranchSlt.PortReads
import Slop.JumpBranchSlt.BranchSoundness
import Slop.Trace.Retirement

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Actual public decoding and native histories discharge every local branch
    interface. Sail determines the branch decision; the checked PC equations
    establish its retirement into the actual native after-state. -/
theorem local_branch_execution {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (active : w 4 = 1) {initial : State} {cells : List Cell} (epoch : Nat)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (leftBound : (Word.mk (w 22).val (w 23).val).Bounded)
    (rightBound : (Word.mk (w 26).val (w 27).val).Bounded)
    (initialAligned : (w 0).val % 4 = 0) (finalHiBound : (w 17).val < limbBase)
    (opcode : SailRV32.bop) (imm : BitVec 13) (rs1 rs2 : BitVec 5)
    (encoding : entry.instruction = .BTYPE (imm, .Regidx rs2, .Regidx rs1, opcode))
    {before after : State} {events : List MemoryAccess}
    (history : Trace.SailHistory cells (nativeEvents epoch w).reverse before after)
    (past : Trace.SailHistory cells events initial before)
    (isa : ∃ value, initial.regs.get? .misa = some value) :
    let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
    let finalPC := (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec
    run (normalStep (SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode))
      (Trace.retiredState before currentPC) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (Trace.retiredState after finalPC) := by
  let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
  let rebased := Trace.retiredState before currentPC
  let finished := Trace.retiredState after currentPC
  have history' := Trace.Proofs.retired_state_history history currentPC
  have csrs := Trace.Proofs.sail_history_control_flow_csrs past
  have limbField : limbBase < p := by dsimp [limbBase]; omega
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
  have canonical := Trace.Proofs.native_query_pc_word limbField query
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at canonical
  have pcBound : (Word.mk (w 0).val (w 1).val).Bounded :=
    canonical.symm ▸ Word.ofBitVec_bound entry.pc
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
  have mapping : Branch.RowWordMapping input output w := by
    constructor
    · exact ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩
    · exact ⟨rfl, rfl, low, high, rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact leftIndex
    · exact rightIndex
  have readLeft := register_reads limbField epoch query history' ⟨0, by decide⟩
  have readRight := register_reads limbField epoch query history' ⟨1, by decide⟩
  have interface : Branch.RowInterfaces input output w := by
    constructor
    · exact active
    · exact selectors.2.2.2.1
    · exact ⟨selectors.1, selectors.2.1, selectors.2.2.1⟩
    · simpa [shape, data] using tag
    · exact selectors.2.2.2.2
    · exact leftBound
    · exact rightBound
    · exact fields.1
    · exact pcBound.1
    · exact initialAligned
    · simpa [encoding] using decoder_offset_even source
    · exact finalHiBound
    · change entry.data.immediate.toBitVec = _
      rw [shape]
      exact Word.ofBitVec_roundtrip _
    · simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.readCode,
        pairCode, Trace.memoryWord, input] using readLeft
    · simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.readCode,
        pairCode, Trace.memoryWord, input] using readRight
    · exact Trace.Proofs.retired_state_pc before currentPC
    · obtain ⟨value, read⟩ := isa
      refine ⟨value, read_register ?_⟩
      simpa [input, rebased, Trace.retiredState, Std.ExtDHashMap.get?_insert] using csrs.1.trans read
  obtain ⟨checkedAfter, normal, projected⟩ := branch_soundness hp input output w
    ⟨interface, h, mapping⟩
  have written := register_write limbField epoch query history'
  have write : run (SailRV32.Functions.wX_bits (.Regidx 0) output.destination.toBitVec) rebased =
      .ok () finished := by
    simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.writeCode,
      pairCode, Trace.memoryWord, output] using written
  have nativeProjection := Trace.Proofs.projected_step_of_write 0 output write
  have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
  rw [same] at normal
  simpa only [Branch.execution, Branch.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, input, output, rebased, finished,
    Trace.Proofs.retired_state_overwrite] using normal

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
    (history : Trace.SailHistory cells (nativeEvents trace.memoryEpoch w).reverse before after)
    (past : Trace.SailHistory cells events initial before)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured initial := by find_configured) :
    let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
    let finalPC := (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec
    run (normalStep (SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode))
      (Trace.retiredState before currentPC) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (Trace.retiredState after finalPC) := by
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have source := Trace.Proofs.program_sources programImage entry present
  have bounds := (native_value_bounds hp inverse accepted clocks image programImage decoded).1 _ member
  have left := bounds importedConstraintsMemoryPorts[0]
    (by simp [Row.ports, importedConstraintsMemoryPorts])
  have leftBound : (Word.mk (w 22).val (w 23).val).Bounded := by
    simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts] using left
  have right := bounds importedConstraintsMemoryPorts[1]
    (by simp [Row.ports, importedConstraintsMemoryPorts])
  have rightBound : (Word.mk (w 26).val (w 27).val).Bounded := by
    simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts] using right
  have finalHi := (trace_pc_bounds limbField accepted decoded terminal _ member).2.2
  have aligned := ((trace_pc_alignment hp accepted initialAligned).1 _ member).1
  exact local_branch_execution hp h (accepted.active _ member) trace.memoryEpoch source query
    leftBound rightBound aligned finalHi opcode imm rs1 rs2 encoding history past isa

end Airbender.JumpBranchSlt.Proofs

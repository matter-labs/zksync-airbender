import Airbender.Proofs.JumpBranchSlt.Values
import Airbender.Proofs.JumpBranchSlt.PortReads
import Airbender.Proofs.Trace.Retirement
import Airbender.Proofs.JumpBranchSlt.Soundness

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

set_option maxHeartbeats 2000000 in
/-- Public-decoded comparisons execute the original Sail clause and retirement
    in their native register history. Operand bounds, preprocessing, selectors
    and PC alignment are derived; canonical terminal PC remains a boundary. -/
theorem local_comparison_execution {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (active : w 4 = 1) {initial : State} {cells : List Cell} (epoch : Nat)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (leftBound : (Word.mk (w 22).val (w 23).val).Bounded)
    (rightBound : (Word.mk (w 26).val (w 27).val).Bounded)
    (initialAligned : (w 0).val % 4 = 0) (finalHiBound : (w 17).val < limbBase)
    (opcode : Comparison.Opcode) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = match opcode with
      | .slt => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLT)
      | .slti => .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTI)
      | .sltu => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLTU)
      | .sltiu => .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTIU))
    {before after : State}
    (history : Trace.SailHistory cells (nativeEvents epoch w).reverse before after) :
    let input : Comparison.Input := ⟨opcode, ⟨(w 22).val, (w 23).val⟩,
      (match opcode with
      | .slt | .sltu => ⟨(w 26).val, (w 27).val⟩
      | .slti | .sltiu => entry.data.immediate),
      ⟨(w 0).val, (w 1).val⟩, .Regidx rs1,
      .Regidx (match opcode with | .slt | .sltu => rs2 | .slti | .sltiu => 0),
      .Regidx rd, imm, Trace.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec⟩
    run (normalStep (Comparison.execution input)) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (Trace.retiredState after (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec) := by
  let currentPC := (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec
  let rebased := Trace.retiredState before currentPC
  let finished := Trace.retiredState after currentPC
  have history' := Trace.Proofs.retired_state_history history currentPC
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  have nonzero : rd ≠ 0 := by
    intro zero
    have fields := source.fields
    rw [encoding] at fields
    cases opcode <;> simp_all [decoderFields]
  let data : DecoderData Unit := match opcode with
    | .slt => ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 4, 2⟩
    | .slti => ⟨(), rs1, 0, rd, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 4, 2⟩
    | .sltu => ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 4, 3⟩
    | .sltiu => ⟨(), rs1, 0, rd, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 4, 3⟩
  have shape : entry.data = data := by
    have fields := source.fields
    rw [encoding] at fields
    cases opcode <;> simp [decoderFields] at fields <;> exact fields.2.symm
  have fields := decoder_field_bounds source.fields
  have flags := decoder_selectors limbField h fields.2.1 query
  have f0 := flags ⟨0, by decide⟩
  have f1 := flags ⟨1, by decide⟩
  have f2 := flags ⟨2, by decide⟩
  have f3 := flags ⟨3, by decide⟩
  have f4 := flags ⟨4, by decide⟩
  have selectors : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 1 ∧ w 14 = 0 ∧ w 15 = 0 := by
    cases opcode <;> simp_all [importedConstraintsDecoderColumns, data, Nat.testBit]
  have canonical := Trace.Proofs.native_query_pc_word limbField query
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at canonical
  have pcBound : (Word.mk (w 0).val (w 1).val).Bounded :=
    canonical.symm ▸ Word.ofBitVec_bound entry.pc
  have indices := Trace.Proofs.native_query_indices limbField query
  have leftIndex : w 5 = (rs1.toNat : ZMod p) := by
    have index := indices.1
    change (w 5).val = entry.data.rs1.toNat at index
    rw [shape] at index
    cases opcode <;>
      exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have rightIndex : w 6 = (entry.data.rs2.toNat : ZMod p) := by
    have index := indices.2.1
    change (w 6).val = entry.data.rs2.toNat at index
    exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have rdIndex : w 7 = (rd.toNat : ZMod p) := by
    have index := indices.2.2
    change (w 7).val = entry.data.rd.toNat at index
    rw [shape] at index
    cases opcode <;>
      exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) index)
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
  have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
  change w 8 = (entry.data.immediate.lo : ZMod p) at low
  change w 9 = (entry.data.immediate.hi : ZMod p) at high
  change w 10 = (entry.data.funct3 : ZMod p) at tag
  have readLeft := register_reads limbField epoch query history' ⟨0, by decide⟩
  have readRight := register_reads limbField epoch query history' ⟨1, by decide⟩
  have rightZero : entry.data.rs2 = 0 → (⟨(w 26).val, (w 27).val⟩ : Word) = ⟨0, 0⟩ := by
    intro zero
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode,
      Trace.memoryWord] at readRight
    rw [zero] at readRight
    change EStateM.Result.ok (0 : BitVec 32) rebased = .ok _ rebased at readRight
    exact Word.eq_zero_of_bounded rightBound (EStateM.Result.ok.inj readRight).1.symm
  let input : Comparison.Input := ⟨opcode, ⟨(w 22).val, (w 23).val⟩,
    (match opcode with
    | .slt | .sltu => ⟨(w 26).val, (w 27).val⟩
    | .slti | .sltiu => entry.data.immediate),
    ⟨(w 0).val, (w 1).val⟩, .Regidx rs1, .Regidx entry.data.rs2, .Regidx rd, imm, rebased⟩
  let output : Output := ⟨⟨(w 30).val, (w 31).val⟩, ⟨(w 16).val, (w 17).val⟩⟩
  have preprocessing : match opcode with
      | .slt | .sltu => w 8 = 0 ∧ w 9 = 0
      | .slti | .sltiu => input.rs2 = zeroRegister ∧ w 26 = 0 ∧ w 27 = 0 := by
    cases opcode
    case slt | sltu => simpa [shape, data] using And.intro low high
    case slti | sltiu =>
      have zero := rightZero (by simp [shape, data])
      have lo : (w 26).val = 0 := congrArg Word.lo zero
      have hi : (w 27).val = 0 := congrArg Word.hi zero
      refine ⟨by simp [input, shape, data, zeroRegister], ?_, ?_⟩
      · exact (ZMod.natCast_zmod_val (w 26)).symm.trans (by rw [lo]; simp)
      · exact (ZMod.natCast_zmod_val (w 27)).symm.trans (by rw [hi]; simp)
  have mapping : Comparison.RowWordMapping input output w := by
    constructor
    · exact (ZMod.natCast_zmod_val _).symm
    · exact (ZMod.natCast_zmod_val _).symm
    · cases opcode
      case slt | sltu => simp [input, preprocessing.1]
      case slti | sltiu => simpa [input, preprocessing.2.1] using low
    · cases opcode
      case slt | sltu => simp [input, preprocessing.2]
      case slti | sltiu => simpa [input, preprocessing.2.2] using high
    · exact leftIndex
    · exact rightIndex
    · exact rdIndex
    all_goals rfl
  have interface : Comparison.RowInterfaces input output w := by
    constructor
    · exact active
    · exact selectors.2.2.1
    · exact ⟨selectors.1, selectors.2.1, selectors.2.2.2.1⟩
    · cases opcode <;> simpa only [input] using preprocessing
    · cases opcode <;> simpa [input, shape, data] using tag
    · exact selectors.2.2.2.2
    · change .Regidx rd ≠ zeroRegister
      simpa [zeroRegister] using nonzero
    · exact leftBound
    · cases opcode
      case slt | sltu => exact rightBound
      case slti | sltiu => exact fields.1
    · exact pcBound.1
    · exact initialAligned
    · exact finalHiBound
    · cases opcode <;> simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.readCode,
        pairCode, Trace.memoryWord, input] using readLeft
    · intro standard
      cases opcode
      case slt | sltu =>
        simpa [importedConstraintsMemoryPorts, MemoryPort.readCode,
          pairCode, Trace.memoryWord, input] using readRight
      case slti | sltiu => simp [input] at standard
    · intro immediate
      cases opcode
      case slt | sltu => simp [input] at immediate
      case slti | sltiu =>
        change entry.data.immediate.toBitVec = _
        rw [shape]
        exact Word.ofBitVec_roundtrip _
    · exact Trace.Proofs.retired_state_pc before currentPC
  obtain ⟨checkedAfter, normal, projected⟩ := comparison_soundness hp input output w
    ⟨interface, h, mapping⟩
  have written := register_write limbField epoch query history'
  have write : run (SailRV32.Functions.wX_bits (.Regidx rd) output.destination.toBitVec) rebased =
      .ok () finished := by
    cases opcode <;> simpa [shape, data, importedConstraintsMemoryPorts, MemoryPort.writeCode,
      pairCode, Trace.memoryWord, output] using written
  have nativeProjection := Trace.Proofs.projected_step_of_write rd output write
  have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
  rw [same] at normal
  cases opcode <;> simpa only [Comparison.execution, Comparison.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, input, output, rebased, finished, currentPC, shape, data,
    Trace.Proofs.retired_state_overwrite] using normal

theorem comparison_rebased_step {p : Nat} [Fact p.Prime]
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
    (opcode : Comparison.Opcode) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = match opcode with
      | .slt => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLT)
      | .slti => .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTI)
      | .sltu => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLTU)
      | .sltiu => .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTIU))
    {before after : State}
    (history : Trace.SailHistory cells (nativeEvents trace.memoryEpoch w).reverse before after) :
    let input : Comparison.Input := ⟨opcode, ⟨(w 22).val, (w 23).val⟩,
      (match opcode with
      | .slt | .sltu => ⟨(w 26).val, (w 27).val⟩
      | .slti | .sltiu => entry.data.immediate),
      ⟨(w 0).val, (w 1).val⟩, .Regidx rs1,
      .Regidx (match opcode with | .slt | .sltu => rs2 | .slti | .sltiu => 0),
      .Regidx rd, imm, Trace.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec⟩
    run (normalStep (Comparison.execution input)) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (Trace.retiredState after (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec) := by
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
  exact local_comparison_execution hp h (accepted.active _ member) trace.memoryEpoch source query
    leftBound rightBound aligned finalHi opcode imm rs1 rs2 rd encoding history

end Airbender.JumpBranchSlt.Proofs

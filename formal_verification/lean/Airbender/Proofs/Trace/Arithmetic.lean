import Airbender.Proofs.Trace.PortReads
import Airbender.Proofs.Trace.Retirement
import Airbender.Proofs.Trace.PC
import Airbender.Proofs.Trace.ProgramImage
import Airbender.Proofs.Trace.Values
import Airbender.Proofs.AddSub.DecodedInterface

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail

-- The existing circuit interface observes native words; instruction behavior
-- remains the original generated Sail clause.
def arithmeticInput {p : Nat} (opcode : Opcode) (rs1 rs2 rd : BitVec 5)
    (immediate : BitVec 12) (upper : BitVec 20) (w : Nat → ZMod p) (before : State) : Input :=
  ⟨⟨opcode, ⟨(w 25).val, (w 26).val⟩, ⟨(w 27).val, (w 28).val⟩,
    ⟨(w 9).val, (w 10).val⟩, ⟨(w 0).val, (w 1).val⟩⟩,
    .Regidx rs1, .Regidx rs2, .Regidx rd, immediate, upper, before⟩

def arithmeticOutput (w : Nat → ZMod p) : Output :=
  ⟨⟨(w 37).val, (w 38).val⟩, ⟨(w 13).val, (w 14).val⟩⟩

/-- Both operands and the immediate are bounded by initialized native history
    and the selected public decoder row, rather than per-row assumptions. -/
theorem arithmetic_row_ranges [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p} {setup : DecoderSetup} {initial : State} {cells : List Cell}
    {count : Nat} (inputs : ImageBoundary trace initial cells)
    (image : IndexedProgram initial count setup.program)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p) ∈ trace.rows) :
    (Word.mk (w 25).val (w 26).val).Bounded ∧
      (Word.mk (w 27).val (w 28).val).Bounded ∧
      (Word.mk (w 9).val (w 10).val).Bounded := by
  have large : limbBase < p := by dsimp [limbBase, timestampBase] at *; omega
  have reads := (image_value_bounds hp inputs accepted decoded).1 _ member
  have left := reads AddSub.importedConstraintsMemoryPorts[0]
    (by change AddSub.importedConstraintsMemoryPorts[0] ∈ AddSub.importedConstraintsMemoryPorts
        simp [AddSub.importedConstraintsMemoryPorts])
  have right := reads AddSub.importedConstraintsMemoryPorts[1]
    (by change AddSub.importedConstraintsMemoryPorts[1] ∈ AddSub.importedConstraintsMemoryPorts
        simp [AddSub.importedConstraintsMemoryPorts])
  rw [read_word] at left right
  exact ⟨left, right, (indexed_decoder_inputs large image accepted decoded _ member).2.1⟩

/-- Original decoded constructors, actual native port reads and canonical words
    discharge the existing local ADD/SUB interface. This internal lemma exposes
    only the control-state representation needed for instruction retirement. -/
theorem local_arithmetic_interface [Fact p.Prime] (hp : limbBase < p)
    {cells : List Cell} (epoch : Nat) {w : Nat → ZMod p}
    (bounds : (Word.mk (w 25).val (w 26).val).Bounded ∧
      (Word.mk (w 27).val (w 28).val).Bounded ∧ (Word.mk (w 9).val (w 10).val).Bounded)
    (pcBound : (Word.mk (w 0).val (w 1).val).Bounded) (aligned : (w 0).val % 4 = 0)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    (opcode : Opcode) (rs1 rs2 rd : BitVec 5) (immediate : BitVec 12) (upper : BitVec 20)
    {before after : State}
    (encoding : entry.instruction = instruction (arithmeticInput opcode rs1 rs2 rd immediate upper w before))
    (history : SailHistory cells (rowEvents epoch (⟨.addSub, w⟩ : Row p)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (Word.mk (w 0).val (w 1).val).toBitVec before) :
    AddSub.InterfaceAssumptions (arithmeticInput opcode rs1 rs2 rd immediate upper w before)
      (arithmeticOutput w) w := by
  let input := arithmeticInput opcode rs1 rs2 rd immediate upper w before
  have data : entry.data = AddSub.Proofs.arithmeticData input := by
    rw [encoding] at fields
    cases opcode <;> exact (Option.some.inj fields).symm
  have offset := native_query_immediate_word hp (decoder_field_bounds fields).1 query
  obtain ⟨left, right⟩ := addsub_history_register_reads hp epoch history query
  simp [AddSub.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord] at left right
  rw [data] at offset left right
  have reference := AddSub.Proofs.reference_interface input bounds.1 bounds.2.1 offset left right pc
  have mask := congrArg (fun q : Vector (ZMod p) 10 => q[9]) query
  have flag := congrArg (fun q : Vector (ZMod p) 10 => q[5]) query
  change w 12 = (entry.data.mask : ZMod p) at mask
  change w 8 = (if entry.data.rd = 0 then 1 else 0) at flag
  rw [data] at mask flag
  constructor
  · cases opcode <;>
      simpa [input, arithmeticInput, AddSub.decodedMask, AddSub.Proofs.arithmeticData,
        arithmeticFields] using mask
  · cases opcode <;>
      simpa [input, arithmeticInput, AddSub.Proofs.arithmeticData, arithmeticFields,
        zeroRegister] using flag
  · exact reference.1
  · intro _; exact ⟨bounds.1, bounds.2.1, bounds.2.2⟩
  · exact pcBound
  · exact aligned
  · exact reference.2

/-- Mapping the existing observable interface needs only the decoded rd index;
    all values and both endpoint PCs are the actual imported columns. -/
theorem arithmetic_mapping [Fact p.Prime] {w : Nat → ZMod p} {before : State}
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    (opcode : Opcode) (rs1 rs2 rd : BitVec 5) (immediate : BitVec 12) (upper : BitVec 20)
    (encoding : entry.instruction = instruction (arithmeticInput opcode rs1 rs2 rd immediate upper w before)) :
    AddSub.RowWordMapping (arithmeticInput opcode rs1 rs2 rd immediate upper w before)
      (arithmeticOutput w) w := by
  have index := congrArg (fun q : Vector (ZMod p) 10 => q[4]) query
  change w 7 = (entry.data.rd.toNat : ZMod p) at index
  have data : entry.data = AddSub.Proofs.arithmeticData
      (arithmeticInput opcode rs1 rs2 rd immediate upper w before) := by
    rw [encoding] at fields
    cases opcode <;> exact (Option.some.inj fields).symm
  rw [data] at index
  have destination : w 7 = (rd.toNat : ZMod p) := by
    cases opcode <;>
      simpa [AddSub.Proofs.arithmeticData, arithmeticInput, arithmeticFields] using index
  constructor
  all_goals first
    | exact destination
    | (simp [arithmeticInput, arithmeticOutput])

/-- Global acceptance/public setup supply every numerical local premise. -/
theorem arithmetic_row_interface [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p} {setup : DecoderSetup} {initial : State} {cells : List Cell}
    {count : Nat} (inputs : ImageBoundary trace initial cells)
    (image : IndexedProgram initial count setup.program)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    (opcode : Opcode) (rs1 rs2 rd : BitVec 5) (immediate : BitVec 12) (upper : BitVec 20)
    {before after : State}
    (encoding : entry.instruction = instruction (arithmeticInput opcode rs1 rs2 rd immediate upper w before))
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row p)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (Word.mk (w 0).val (w 1).val).toBitVec before) :
    AddSub.InterfaceAssumptions (arithmeticInput opcode rs1 rs2 rd immediate upper w before)
      (arithmeticOutput w) w := by
  have large : limbBase < p := by dsimp [limbBase, timestampBase] at *; omega
  exact local_arithmetic_interface large trace.memoryEpoch
    (arithmetic_row_ranges hp inputs image accepted decoded member)
    (indexed_decoder_inputs large image accepted decoded _ member).1
    (indexed_decoder_inputs large image accepted decoded _ member).2.2
    fields query opcode rs1 rs2 rd immediate upper encoding history pc

/-- Original Sail preparation/execution/retirement reaches the actual native
    destination update with the native final PC. The state is derived from the
    native history and projected Sail write, rather than supplied as a result. -/
theorem arithmetic_row_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p} {setup : DecoderSetup} {initial : State} {cells : List Cell}
    {count : Nat} (inputs : ImageBoundary trace initial cells)
    (image : IndexedProgram initial count setup.program)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    (opcode : Opcode) (rs1 rs2 rd : BitVec 5) (immediate : BitVec 12) (upper : BitVec 20)
    {before after : State}
    (encoding : entry.instruction = instruction (arithmeticInput opcode rs1 rs2 rd immediate upper w before))
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row p)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (Word.mk (w 0).val (w 1).val).toBitVec before) :
    run (normalStep (execution (arithmeticInput opcode rs1 rs2 rd immediate upper w before))) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (arithmeticOutput w).pc.toBitVec) := by
  have large : limbBase < p := by dsimp [limbBase, timestampBase] at *; omega
  have interface := arithmetic_row_interface hp inputs image accepted decoded member fields query
    opcode rs1 rs2 rd immediate upper encoding history pc
  have mapping := arithmetic_mapping fields query opcode rs1 rs2 rd immediate upper encoding
  obtain ⟨checkedAfter, normal, projected⟩ := AddSub.Proofs.soundness
    (by dsimp [timestampBase] at hp; omega) _ _ w
    ⟨interface, accepted.constraints _ member, mapping⟩
  have written := addsub_history_register_write large trace.memoryEpoch history query
  have destination : entry.data.rd = rd := by
    rw [encoding] at fields
    cases opcode <;> exact congrArg DecoderData.rd (Option.some.inj fields).symm
  rw [destination] at written
  simp [AddSub.importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord] at written
  have nativeProjection := projected_step_of_write rd (arithmeticOutput w) written
  have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
  rw [same] at normal
  exact normal

/-- Actual control-register transport supplies the row PC read. Repeated
    retirement overwrites controls while retaining the derived native data state. -/
theorem arithmetic_rebased_step [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p} {setup : DecoderSetup} {initial : State} {cells : List Cell}
    {count : Nat} (inputs : ImageBoundary trace initial cells)
    (image : IndexedProgram initial count setup.program)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    (opcode : Opcode) (rs1 rs2 rd : BitVec 5) (immediate : BitVec 12) (upper : BitVec 20)
    {before after : State}
    (encoding : entry.instruction = instruction (arithmeticInput opcode rs1 rs2 rd immediate upper w before))
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row p)).reverse before after) :
    run (normalStep (execution (arithmeticInput opcode rs1 rs2 rd immediate upper w before)))
      (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (arithmeticOutput w).pc.toBitVec) := by
  have rebased := arithmetic_row_execution
    (before := retiredState before (Word.mk (w 0).val (w 1).val).toBitVec)
    hp inputs image accepted decoded member fields query
    opcode rs1 rs2 rd immediate upper encoding
    (retired_state_history history (Word.mk (w 0).val (w 1).val).toBitVec)
    (retired_state_pc _ _)
  rw [retired_state_overwrite] at rebased
  exact rebased

/-- Select the original Sail clause from the actual five-opcode decoder result.
    All operands, ranges, preprocessing and control effects remain derived. -/
theorem arithmetic_instruction_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p} {setup : DecoderSetup} {initial : State} {cells : List Cell}
    {count : Nat} (inputs : ImageBoundary trace initial cells)
    (image : IndexedProgram initial count setup.program)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    {before after : State}
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row p)).reverse before after) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (arithmeticOutput w).pc.toBitVec) := by
  have arithmetic (opcode : Opcode) (rs1 rs2 rd : BitVec 5)
      (imm : BitVec 12) (upper : BitVec 20)
      (encoding : entry.instruction = instruction (arithmeticInput opcode rs1 rs2 rd imm upper w before)) :
      ∃ clause, registerClause entry.instruction = some clause ∧
        run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
          .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (arithmeticOutput w).pc.toBitVec) := by
    have checked := arithmetic_rebased_step hp inputs image accepted decoded member fields query
      opcode rs1 rs2 rd imm upper encoding history
    cases opcode
    all_goals refine ⟨_, ?_, checked⟩
    all_goals rw [encoding]; rfl
  unfold decoderFields at fields
  split at fields
  case h_1 => rename_i _ rs2 rs1 rd encoding; exact arithmetic .add rs1 rs2 rd 0 0 encoding
  case h_2 => rename_i _ rs2 rs1 rd encoding; exact arithmetic .sub rs1 rs2 rd 0 0 encoding
  case h_3 => rename_i _ imm rs1 rd encoding; exact arithmetic .addi rs1 0 rd imm 0 encoding
  case h_4 => rename_i _ imm rd encoding; exact arithmetic .lui 0 0 rd 0 imm encoding
  case h_5 => rename_i _ imm rd encoding; exact arithmetic .auipc 0 0 rd 0 imm encoding
  case h_6 => cases fields

end Airbender.Trace.Proofs

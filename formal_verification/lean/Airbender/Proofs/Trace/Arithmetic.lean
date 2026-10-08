import Airbender.Proofs.Trace.PortReads
import Airbender.Proofs.Trace.ROM
import Airbender.Proofs.Trace.PC
import Airbender.Proofs.Trace.Retirement
import Airbender.Proofs.AddSub

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Both arithmetic operands and the immediate are bounded by the accepted
    history and actual decoder metadata; they are no longer per-row premises. -/
theorem arithmetic_row_ranges [Fact p.Prime] (hp : ROM.limit < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query) :
    (Word.mk (w 25).val (w 26).val).Bounded ∧
      (Word.mk (w 29).val (w 30).val).Bounded ∧
      (Word.mk (w 8).val (w 9).val).Bounded := by
  have clockSize : 2 * timestampBase + 4 < p := by
    dsimp [ROM.limit, timestampBase] at *; omega
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at *; omega
  have reads := read_bounds clockSize inverse accepted boundary
    (ROM.Proofs.value_boundary limbSize image setup) _ member
  have left := reads AddSub.importedConstraintsMemoryPorts[0]
    (by simp [Row.ports, AddSub.importedConstraintsMemoryPorts])
  have right := reads AddSub.importedConstraintsMemoryPorts[1]
    (by simp [Row.ports, AddSub.importedConstraintsMemoryPorts])
  rw [read_word] at left right
  exact ⟨left, right, query_immediate limbSize fields query⟩

private theorem bounded_zero {word : Word} (bounded : word.Bounded)
    (zero : word.toBitVec = 0) : word = ⟨0, 0⟩ := by
  have value := congrArg BitVec.toNat zero
  rw [Word.toBitVec_toNat bounded] at value
  change word.lo + limbBase * word.hi = 0 at value
  have low : word.lo = 0 := by omega
  have high : word.hi = 0 := by dsimp [limbBase] at value; omega
  cases word
  simp_all

/-- Decoder-selected x0 ports read the native Sail zero register. The derived
    limb bounds recover the full zero-word preprocessing, not just its bits. -/
theorem arithmetic_zero_source [Fact p.Prime] (hp : ROM.limit < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    {before after : State}
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row p)).reverse before after) :
    (entry.data.rs1 = 0 → Word.mk (w 25).val (w 26).val = ⟨0, 0⟩) ∧
      (entry.data.rs2 = 0 → Word.mk (w 29).val (w 30).val = ⟨0, 0⟩) := by
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at *; omega
  have bounds := arithmetic_row_ranges hp inverse accepted boundary image setup member fields query
  have left := row_history_source_read limbSize trace.memoryEpoch history query
    (port := AddSub.importedConstraintsMemoryPorts[0]) rfl
  simp [AddSub.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode,
    memoryWord] at left
  have right := (addsub_history_registers limbSize query trace.memoryEpoch history).1
  constructor
  · intro zero
    rw [zero] at left
    change EStateM.Result.ok (0 : BitVec 32) before = .ok _ before at left
    exact bounded_zero bounds.1 (EStateM.Result.ok.inj left).1.symm
  · intro zero
    rw [zero] at right
    change EStateM.Result.ok (0 : BitVec 32) before = .ok _ before at right
    exact bounded_zero bounds.2.1 (EStateM.Result.ok.inj right).1.symm

-- Assemble the existing family interface from native columns. This is proof
-- plumbing: instruction behavior continues to be Sail.execution.
private def arithmeticInput {p : Nat} (opcode : Opcode) (rs1 rs2 rd : BitVec 5)
    (immediate : BitVec 12) (upper : BitVec 20) (w : Nat → ZMod p) (before : State) : Input :=
  ⟨⟨opcode, ⟨(w 25).val, (w 26).val⟩, ⟨(w 29).val, (w 30).val⟩,
    ⟨(w 8).val, (w 9).val⟩, ⟨(w 0).val, (w 1).val⟩⟩,
    .Regidx rs1, .Regidx rs2, .Regidx rd, immediate, upper, before⟩

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Discharge the arithmetic family's interfaces from the actual decoded
    constructor, public initialization and grouped native transfers. Original
    sources erased by x0 preprocessing are read from the initialized history. -/
theorem arithmetic_row_interface [Fact p.Prime] (hp : ROM.limit < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (initialPC : trace.initial.word.Bounded)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    (opcode : Opcode) (rs1 rs2 rd : BitVec 5) (immediate : BitVec 12) (upper : BitVec 20)
    (sources : Cell.register rs1 ∈ cells ∧ Cell.register rs2 ∈ cells)
    (encoding : entry.instruction = match opcode with
      | .add => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)
      | .addi => .ITYPE (immediate, .Regidx rs1, .Regidx rd, .ADDI)
      | .sub => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB)
      | .lui => .UTYPE (upper, .Regidx rd, .LUI)
      | .auipc => .UTYPE (upper, .Regidx rd, .AUIPC))
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row p)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (Word.mk (w 0).val (w 1).val).toBitVec before) :
    AddSub.InterfaceAssumptions (arithmeticInput opcode rs1 rs2 rd immediate upper w before)
      ⟨⟨(w 33).val, (w 34).val⟩, ⟨(w 19).val, (w 20).val⟩⟩ w := by
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at *; omega
  let data : DecoderData := match opcode with
    | .add => arithmeticFields rs1 rs2 rd 0 1
    | .addi => arithmeticFields rs1 0 rd (SailRV32.Functions.sign_extend (m := 32) immediate) 1
    | .sub => arithmeticFields rs1 rs2 rd 0 2
    | .lui => arithmeticFields 0 0 rd (upper ++ BitVec.ofNat 12 0) 1
    | .auipc => arithmeticFields 0 0 rd (upper ++ BitVec.ofNat 12 0) 4
  have decoded : entry.data = data := by
    rw [encoding] at fields
    cases opcode <;> exact (Option.some.inj fields).symm
  have flags := query_selectors limbSize accepted member fields query
  change ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] =
    if entry.data.mask.testBit i.val then 1 else 0 at flags
  rw [decoded] at flags
  have bounds := arithmetic_row_ranges hp inverse accepted boundary image setup member fields query
  have zeros := arithmetic_zero_source hp inverse accepted boundary image setup member fields query history
  rw [decoded] at zeros
  have offset := query_immediate_value limbSize fields query
  change Word.mk (w 8).val (w 9).val = entry.data.immediate at offset
  rw [decoded] at offset
  have left := row_history_source_read limbSize trace.memoryEpoch history query
    (port := AddSub.importedConstraintsMemoryPorts[0]) rfl
  simp [AddSub.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord] at left
  have right := (addsub_history_registers limbSize query trace.memoryEpoch history).1
  rw [decoded] at left right
  have discardedLeft := image_register_after_history image past rs1 sources.1
  have discardedRight := image_register_after_history image past rs2 sources.2
  dsimp only [data, arithmeticFields] at flags zeros offset left right
  constructor
  · constructor
    · exact accepted.active _ member
    · have flag := flags ⟨0, by decide⟩
      cases opcode <;> by_cases zero : rd = (0#5) <;>
        simpa [arithmeticInput, data, arithmeticFields, zero, zeroRegister,
          Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
    · have flag := flags ⟨1, by decide⟩
      cases opcode <;> by_cases zero : rd = (0#5) <;>
        simpa [arithmeticInput, data, arithmeticFields, zero, zeroRegister,
          Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
    · intro k lower upperBound
      have flag := flags ⟨k - 10, by omega⟩
      interval_cases k
      all_goals cases opcode <;> by_cases zero : rd = (0#5)
      all_goals simpa [arithmeticInput, data, arithmeticFields, zero, zeroRegister,
        Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
    · by_cases zero : rd = (0#5)
      · have leftZero := zeros.1 (by cases opcode <;> simp [zero])
        have rightZero := zeros.2 (by cases opcode <;> simp [zero])
        have immediateZero : Word.mk (w 8).val (w 9).val = ⟨0, 0⟩ := by
          cases opcode <;> simpa [zero] using offset
        simpa [AddSub.Preprocessing, arithmeticInput, zero, zeroRegister] using
          And.intro leftZero (And.intro rightZero immediateZero)
      · have nonzero : SailRV32.regidx.Regidx rd ≠ zeroRegister := by
          simpa [zeroRegister] using zero
        dsimp only [AddSub.Preprocessing, arithmeticInput]
        rw [if_neg nonzero]
        cases opcode
        · simpa [zero, Word.ofBitVec] using offset
        · exact zeros.2 (by simp [zero])
        · simpa [zero, Word.ofBitVec] using offset
        · exact ⟨zeros.1 (by simp [zero]),
            zeros.2 (by simp [zero])⟩
        · exact ⟨zeros.1 (by simp [zero]),
            zeros.2 (by simp [zero])⟩
  · intro _
    exact ⟨bounds.1, bounds.2.1, bounds.2.2⟩
  · exact (trace_pc_bounds accepted initialPC).1 _ member |>.1
  · constructor
    · intro used
      by_cases zero : rd = (0#5)
      · obtain ⟨value, read⟩ := discardedLeft
        exact ⟨value, read, by simp [arithmeticInput, zeroRegister, zero]⟩
      · cases opcode <;> simp only [arithmeticInput] at used
        all_goals first
          | (solve | simp at used)
          | (exact ⟨_, by simpa [zero, arithmeticInput] using left, fun _ => rfl⟩)
    · intro used
      by_cases zero : rd = (0#5)
      · obtain ⟨value, read⟩ := discardedRight
        exact ⟨value, read, by simp [arithmeticInput, zeroRegister, zero]⟩
      · cases opcode <;> simp only [arithmeticInput] at used
        all_goals first
          | (solve | simp at used)
          | (exact ⟨_, by simpa [zero, arithmeticInput] using right, fun _ => rfl⟩)
    · intro nonzero used
      have zero : rd ≠ (0#5) := by simpa [arithmeticInput, zeroRegister] using nonzero
      change opcode = .addi at used
      subst opcode
      have value := congrArg Word.toBitVec offset
      simpa [zero, Word.ofBitVec_roundtrip, arithmeticInput] using value
    · intro nonzero used
      have zero : rd ≠ (0#5) := by simpa [arithmeticInput, zeroRegister] using nonzero
      change opcode = .lui ∨ opcode = .auipc at used
      rcases used with rfl | rfl
      all_goals
        have value := congrArg Word.toBitVec offset
        simpa [zero, Word.ofBitVec_roundtrip, arithmeticInput,
          SailRV32.Functions.sign_extend, Sail.BitVec.signExtend] using value
    · exact pc

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every selected arithmetic constructor executes to the native row update
    through Sail's own preparation and retirement. Operand/read/selector/range
    contracts are conclusions of the accepted trace, not additional premises. -/
theorem arithmetic_row_execution [Fact p.Prime] (hp : ROM.limit < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (initialPC : trace.initial.word.Bounded)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    (opcode : Opcode) (rs1 rs2 rd : BitVec 5) (immediate : BitVec 12) (upper : BitVec 20)
    (sources : Cell.register rs1 ∈ cells ∧ Cell.register rs2 ∈ cells)
    (encoding : entry.instruction = match opcode with
      | .add => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)
      | .addi => .ITYPE (immediate, .Regidx rs1, .Regidx rd, .ADDI)
      | .sub => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB)
      | .lui => .UTYPE (upper, .Regidx rd, .LUI)
      | .auipc => .UTYPE (upper, .Regidx rd, .AUIPC))
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row p)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (Word.mk (w 0).val (w 1).val).toBitVec before) :
    let finalPC := (Word.mk (w 19).val (w 20).val).toBitVec
    run (normalStep (execution (arithmeticInput opcode rs1 rs2 rd immediate upper w before))) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { after with regs := after.regs.insert .nextPC finalPC |>.insert .PC finalPC } := by
  let input := arithmeticInput opcode rs1 rs2 rd immediate upper w before
  let output : Output := ⟨⟨(w 33).val, (w 34).val⟩, ⟨(w 19).val, (w 20).val⟩⟩
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at *; omega
  have destination : entry.data.rd = rd := by
    rw [encoding] at fields
    cases opcode
    all_goals
      simp only [decoderFields, Option.some.injEq] at fields
      rw [← fields]
      unfold arithmeticFields
      split <;> simp_all
  have index := (query_register_indices limbSize query).2.2
  change (w 7).val = entry.data.rd.toNat at index
  have rdColumn : w 7 = (rd.toNat : ZMod p) := by
    calc
      w 7 = ((w 7).val : ZMod p) := (ZMod.natCast_zmod_val _).symm
      _ = (rd.toNat : ZMod p) := by rw [index, destination]
  have mapping : AddSub.WordMapping input output w := by
    constructor
    all_goals first
      | exact (ZMod.natCast_zmod_val _).symm
      | exact rdColumn
      | rfl
  have interface := arithmetic_row_interface hp inverse accepted boundary image setup
    initialPC member fields query opcode rs1 rs2 rd immediate upper sources encoding past history pc
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
  have addressInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  obtain ⟨checkedAfter, normal, projected⟩ := AddSub.Proofs.soundness
    (by dsimp [ROM.limit] at hp; omega) addressInverse input output w ⟨interface, core, mapping⟩
  have written := (addsub_history_registers limbSize query trace.memoryEpoch history).2
  rw [destination] at written
  have prepared := cell_write_control .nextPC (.inr rfl) output.pc.toBitVec
    (.register rd) output.destination.toBitVec written
  change run (SailRV32.Functions.wX_bits (.Regidx rd) output.destination.toBitVec) _ = _ at prepared
  have nativeProjection : run (projectedStep (.Regidx rd) output) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { after with regs := after.regs.insert .nextPC output.pc.toBitVec |>.insert .PC output.pc.toBitVec } := by
    simp only [projectedStep, writeResult, freeM_bind_assoc, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ (write_register .nextPC output.pc.toBitVec before)]
    rw [run_bind_of_ok _ _ _ _ _ prepared]
    rw [run_bind_of_ok _ _ _ _ _ (write_register .PC output.pc.toBitVec
      { after with regs := after.regs.insert .nextPC output.pc.toBitVec })]
    rfl
  have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
  rw [same] at normal
  exact normal

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Transport the native row through its actual Sail boundary state. The PC
    read is derived from that state, and repeated retirement collapses to the
    new native PC. Complete path composition supplies the boundary ordering. -/
theorem arithmetic_rebased_step [Fact p.Prime] (hp : ROM.limit < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (initialPC : trace.initial.word.Bounded)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    (opcode : Opcode) (rs1 rs2 rd : BitVec 5) (immediate : BitVec 12) (upper : BitVec 20)
    (sources : Cell.register rs1 ∈ cells ∧ Cell.register rs2 ∈ cells)
    (encoding : entry.instruction = match opcode with
      | .add => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)
      | .addi => .ITYPE (immediate, .Regidx rs1, .Regidx rd, .ADDI)
      | .sub => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB)
      | .lui => .UTYPE (upper, .Regidx rd, .LUI)
      | .auipc => .UTYPE (upper, .Regidx rd, .AUIPC))
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row p)).reverse before after)
    :
    let currentPC := (Word.mk (w 0).val (w 1).val).toBitVec
    let finalPC := (Word.mk (w 19).val (w 20).val).toBitVec
    run (normalStep (execution
      (arithmeticInput opcode rs1 rs2 rd immediate upper w (retiredState before currentPC))))
      (retiredState before currentPC) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after finalPC) := by
  let currentPC := (Word.mk (w 0).val (w 1).val).toBitVec
  let finalPC := (Word.mk (w 19).val (w 20).val).toBitVec
  have checked := arithmetic_row_execution hp inverse accepted boundary
    (retired_state_image image currentPC) setup initialPC member fields query
    opcode rs1 rs2 rd immediate upper sources encoding
    (retired_state_history past currentPC) (retired_state_history history currentPC)
    (retired_state_pc before currentPC)
  change run (normalStep (execution
      (arithmeticInput opcode rs1 rs2 rd immediate upper w (retiredState before currentPC))))
      (retiredState before currentPC) =
    .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (retiredState after currentPC) finalPC) at checked
  rw [retired_state_overwrite] at checked
  exact checked

end Airbender.Trace.Proofs

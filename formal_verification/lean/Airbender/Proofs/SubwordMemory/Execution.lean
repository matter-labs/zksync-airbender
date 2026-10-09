import Airbender.Proofs.SubwordMemory.Address
import Airbender.Proofs.SubwordMemory.Soundness
import Airbender.Proofs.Trace.Retirement
import Airbender.Proofs.Trace.CodeHistory
import Airbender.Review.Trace.Execution

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

-- These select upstream constructors and native columns, not instruction semantics.
def rowInstruction (store byte signed : Bool) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5) :
    SailRV32.instruction :=
  if store then .STORE (imm, .Regidx rs2, .Regidx rs1, if byte then 1 else 2)
  else .LOAD (imm, .Regidx rs1, .Regidx rd, !signed, if byte then 1 else 2)

def rowData (store byte signed : Bool) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5) : DecoderData Unit :=
  ⟨(), rs1, if store then rs2 else 0, if store then 0 else rd,
    Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),
    (if store then 1 else 0) + (if byte then 2 else 0) + (if signed && !store then 4 else 0), 0⟩

theorem row_decoder_shape {entry : ProgramEntry} (store byte signed : Bool)
    (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = rowInstruction store byte signed imm rs1 rs2 rd)
    (fields : decoderFields entry.instruction = some entry.data) :
    entry.data = rowData store byte signed imm rs1 rs2 rd := by
  rw [encoding] at fields
  cases store <;> cases byte <;> cases signed
  all_goals simp [rowInstruction, decoderFields] at fields
  all_goals simp_all [rowData]

def rowInput (store byte signed : Bool) (imm : BitVec 12) (data : DecoderData Unit)
    (w : Nat → ZMod p) (before : State) : Input :=
  ⟨store, byte, signed && !store, ⟨(w 19).val, (w 20).val⟩, ⟨(w 8).val, (w 9).val⟩,
    ⟨(w 25).val, (w 26).val⟩, ⟨(w 31).val, (w 32).val⟩, ⟨(w 0).val, (w 1).val⟩,
    .Regidx data.rs1, .Regidx data.rs2, .Regidx data.rd, imm,
    Trace.Proofs.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec⟩

def rowOutput (store : Bool) (w : Nat → ZMod p) : Output :=
  ⟨⟨(if store then w 27 else w 21).val, (if store then w 28 else w 22).val⟩,
    ⟨(w 33).val, (w 34).val⟩, ⟨(w 13).val, (w 14).val⟩⟩

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Shared subword retirement over the imported constraints and actual port
    history. Bounds/address/ROM facts are supplied by the global history proof. -/
theorem local_execution {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {program : Nat → BitVec 32} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Verification.subwordTable program)))
    (active : w 4 = 1) {cells : List Cell} (epoch : Nat)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (store byte signed : Bool) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = rowInstruction store byte signed imm rs1 rs2 rd)
    (selected : w 10 = if store then 1 else 0)
    (bounds : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded)
    (address :
      let cell : Word := ⟨(if store then w 27 else w 21).val, (if store then w 28 else w 22).val⟩
      let offset := (w 35).val + 2 * (w 36).val
      cell.Bounded ∧ cell.value % 4 = 0 ∧ offset < 4 ∧
        cell.toBitVec + BitVec.ofNat 32 offset =
          (Word.mk (w 19).val (w 20).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec ∧
        ((Word.mk (w 19).val (w 20).val).toBitVec +
          (Word.mk (w 8).val (w 9).val).toBitVec).toNat % 4 = offset ∧ Cell.ram cell.toBitVec ∈ cells)
    (addressCode :
      let port := if store then importedConstraintsMemoryPorts[2] else importedConstraintsMemoryPorts[1]
      port.address.code w = (Cell.ram (port.address.word w).toBitVec).addressCode)
    {before after : State} (configuration : FlatMemoryConfiguration before)
    (romReads : ∀ cell : Word, cell.Bounded → cell.hi < 64 → Cell.ram cell.toBitVec ∈ cells →
      (readBytes (ue := SailRV32.exception) 4 cell.toBitVec.toNat).run
        (Trace.Proofs.retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
      .ok (program (cell.value / 4))
        (Trace.Proofs.retiredState before (Word.mk (w 0).val (w 1).val).toBitVec))
    (history : Trace.Proofs.SailHistory cells (nativeEvents epoch w).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause)
        (Trace.Proofs.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (Trace.Proofs.retiredState after (⟨(w 13).val, (w 14).val⟩ : Word).toBitVec) := by
  let input := rowInput store byte signed imm entry.data w before
  let output := rowOutput store w
  let currentPC := input.pc.toBitVec
  have history' := Trace.Proofs.retired_state_history history currentPC
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  have nativeRead (mode : Bool) (select : w 10 = if mode then 1 else 0)
      {before after : State}
      (hist : Trace.Proofs.SailHistory cells (nativeEvents epoch w).reverse before after) :
      let port := (if mode then importedConstraintsMemoryPorts[2] else importedConstraintsMemoryPorts[1])
      (readBytes (ue := SailRV32.exception) 4 (port.address.word w).toBitVec.toNat).run before =
        .ok (Trace.Proofs.memoryWord (port.readCode w)) before := by
    have same : mode = store := by
      cases mode <;> cases store <;> simp_all
    subst mode
    exact Trace.Proofs.native_history_read epoch rfl rfl rfl hist
      (by cases store <;> simp [importedConstraintsMemoryPorts]) addressCode
  have nativeWrite (select : w 10 = 1) {before after : State}
      (hist : Trace.Proofs.SailHistory cells (nativeEvents epoch w).reverse before after) :
      run (writeMemory (size := 4) (importedConstraintsMemoryPorts[2].address.word w).toBitVec
        (Trace.Proofs.memoryWord (importedConstraintsMemoryPorts[2].writeCode w))) before = .ok () after := by
    have mode : store = true := by cases store <;> simp_all
    subst store
    exact Trace.Proofs.native_history_write epoch rfl rfl rfl hist rfl addressCode
  have shape := row_decoder_shape store byte signed imm rs1 rs2 rd encoding fields
  have flags := decoder_selectors limbField h (decoder_field_bounds fields).2.1 query
  have selected : w 10 = if store then 1 else 0 := by
    have flag := flags 0
    cases store <;> cases byte <;> cases signed <;>
      simpa [shape, rowData, importedConstraintsDecoderColumns, Nat.testBit] using flag
  have byteSelection : w 11 = if byte then 1 else 0 := by
    have flag := flags 1
    cases store <;> cases byte <;> cases signed <;>
      simpa [shape, rowData, importedConstraintsDecoderColumns, Nat.testBit] using flag
  have signedSelection : w 12 = if signed && !store then 1 else 0 := by
    have flag := flags 2
    cases store <;> cases byte <;> cases signed <;>
      simpa [shape, rowData, importedConstraintsDecoderColumns, Nat.testBit] using flag
  have sourceBound := bounds importedConstraintsMemoryPorts[0] (by simp [importedConstraintsMemoryPorts])
  have readBound := bounds importedConstraintsMemoryPorts[1] (by simp [importedConstraintsMemoryPorts])
  have oldBound := bounds importedConstraintsMemoryPorts[2] (by simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at sourceBound readBound oldBound
  change input.source.Bounded at sourceBound
  change input.readData.Bounded at readBound
  change input.oldData.Bounded at oldBound
  have cellBound : output.cell.Bounded := address.1
  have cellPresent : Cell.ram output.cell.toBitVec ∈ cells := address.2.2.2.2.2
  have cellIndex : (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 =
      output.cell.toBitVec.toNat := by
    change ((Word.mk (w 19).val (w 20).val).toBitVec +
      (Word.mk (w 8).val (w 9).val).toBitVec).toNat / 4 * 4 = _
    rw [← address.2.2.2.1]
    exact aligned_cell_index cellBound address.2.1 address.2.2.1
  have aligned : (input.source.toBitVec + input.immediate.toBitVec).toNat % (if byte then 1 else 2) = 0 := by
    cases byte
    · have low := halfword_aligned h byteSelection
      change w 35 = 0 at low
      have remainder := address.2.2.2.2.1
      change (input.source.toBitVec + input.immediate.toBitVec).toNat % 4 =
        (w 35).val + 2 * (w 36).val at remainder
      rw [low, ZMod.val_zero, zero_add] at remainder
      change (input.source.toBitVec + input.immediate.toBitVec).toNat % 2 = 0
      omega
    · change _ % 1 = 0; exact Nat.mod_one _
  have domain : OrdinaryWordAddress (input.source.toBitVec + input.immediate.toBitVec) := by
    change OrdinaryWordAddress ((Word.mk (w 19).val (w 20).val).toBitVec +
      (Word.mk (w 8).val (w 9).val).toBitVec)
    rw [← address.2.2.2.1]
    exact ordinary_cell_offset (by rw [Word.toBitVec_toNat cellBound]; exact address.2.1)
      (ordinary _ cellPresent) address.2.2.1
  have immediate := Trace.Proofs.native_query_immediate_word limbField (decoder_field_bounds fields).1 query
  change input.immediate = entry.data.immediate at immediate
  have pcWord := Trace.Proofs.native_query_pc_word limbField query
  change input.pc = Word.ofBitVec entry.pc at pcWord
  have indices := Trace.Proofs.native_query_indices limbField query
  change (w 5).val = entry.data.rs1.toNat ∧ (w 6).val = entry.data.rs2.toNat ∧
    (w 7).val = entry.data.rd.toNat at indices
  have mapping : RowWordMapping input output w := by
    constructor
    all_goals dsimp only [input, output, rowInput, rowOutput]
    all_goals first | rfl | exact (ZMod.natCast_zmod_val _).symm |
      exact fun _ => (ZMod.natCast_zmod_val _).symm |
      exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) indices.1) |
      exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) indices.2.1) |
      exact (ZMod.natCast_zmod_val _).symm.trans (congrArg (fun n : Nat => (n : ZMod p)) indices.2.2)
  have interface : RowInterfaces program input output w := by
    constructor
    · exact active
    · exact selected
    · exact byteSelection
    · exact signedSelection
    · exact sourceBound
    · exact immediate.symm ▸ (decoder_field_bounds fields).1
    · intro _; exact readBound
    · intro _; exact oldBound
    · exact pcWord.symm ▸ Word.ofBitVec_bound entry.pc
    · exact cellBound.2
    · simpa [input, rowInput, importedConstraintsMemoryPorts, Trace.Proofs.memoryWord,
        MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, currentPC] using
        source_read limbField epoch query history'
    · intro mode
      change store = _ at mode
      subst store
      simpa [input, rowInput, importedConstraintsMemoryPorts, Trace.Proofs.memoryWord,
        MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, currentPC] using
        register_read limbField true epoch h selected query history'
    · intro mode _
      change store = _ at mode
      subst store
      change (readBytes (ue := SailRV32.exception) 4 _).run input.before = _
      rw [cellIndex]
      simpa [input, output, rowInput, rowOutput, importedConstraintsMemoryPorts, MemoryAddress.word,
        Trace.Proofs.memoryWord, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, currentPC] using
        nativeRead false selected history'
    · intro _ inside
      exact romReads output.cell cellBound inside cellPresent
    · intro mode
      change store = _ at mode
      subst store
      change (readBytes (ue := SailRV32.exception) 4 _).run input.before = _
      rw [cellIndex]
      simpa [input, output, rowInput, rowOutput, importedConstraintsMemoryPorts, MemoryAddress.word,
        Trace.Proofs.memoryWord, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, currentPC] using
        nativeRead true selected history'
    · rw [immediate, shape]
      exact Word.ofBitVec_roundtrip _
    · exact Trace.Proofs.retired_state_pc before currentPC
    · exact memory_access
        (Trace.Proofs.retired_state_configuration configuration currentPC)
        aligned domain
  have addressInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  have checked := soundness hp addressInverse program input output w ⟨interface, h, mapping⟩
  cases mode : store
  · have inputMode : input.store = false := mode
    simp only [spec, inputMode, Bool.false_eq_true, if_false] at checked
    change _ ∧ stepSpec input.before (execution input) input.rd ⟨output.data, output.pc⟩ at checked
    obtain ⟨_, checkedAfter, normal, projected⟩ := checked
    have selectedLoad : w 10 = 0 := by simpa only [mode, Bool.false_eq_true, if_false] using selected
    have written := destination_write limbField epoch h selectedLoad query history'
    have write : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd) output.data.toBitVec)
        input.before = .ok () (Trace.Proofs.retiredState after currentPC) := by
      simpa [input, rowInput, currentPC, output, rowOutput, mode, importedConstraintsMemoryPorts, Trace.Proofs.memoryWord,
        MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate] using written
    have nativeProjection := Trace.Proofs.projected_step_of_write entry.data.rd ⟨output.data, output.pc⟩ write
    have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
    rw [same] at normal
    refine ⟨execution input, ?_, ?_⟩
    · rw [encoding]
      cases byte <;> simp [execution, input, rowInput, rowInstruction, instructionClause, shape, rowData, mode]
    · simpa [input, output, rowInput, rowOutput, currentPC, Trace.Proofs.retired_state_overwrite] using normal
  · have inputMode : input.store = true := mode
    simp only [spec, inputMode, if_true] at checked
    change _ ∧ stepSpec input.before (execution input) zeroRegister ⟨⟨0, 0⟩, output.pc⟩
      (writeMemory (size := 4) output.cell.toBitVec output.data.toBitVec) at checked
    obtain ⟨_, checkedAfter, normal, projected⟩ := checked
    have selectedStore : w 10 = 1 := by simpa only [mode, if_true] using selected
    have written := nativeWrite selectedStore history'
    have write : run ((Cell.ram output.cell.toBitVec).write output.data.toBitVec)
        input.before = .ok () (Trace.Proofs.retiredState after currentPC) := by
      simpa [input, rowInput, currentPC, output, rowOutput, mode, importedConstraintsMemoryPorts, Trace.Proofs.memoryWord,
        MemoryAddress.word, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate, Cell.write] using written
    have nativeProjection := Trace.Proofs.projected_step_of_cell_write
      (.ram output.cell.toBitVec) output.data.toBitVec output.pc write
    have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
    rw [same] at normal
    refine ⟨execution input, ?_, ?_⟩
    · rw [encoding]
      cases byte <;> simp [execution, input, rowInput, rowInstruction, instructionClause, shape, rowData, mode]
    · simpa [input, output, rowInput, rowOutput, currentPC, Trace.Proofs.retired_state_overwrite] using normal

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- RAM loads/stores reach the actual native after-state. All operand ranges,
    reads, decoding and virtual transport are derived from the accepted history.
    The address-domain restriction is on public initialized cells. -/
theorem row_ram_execution {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {program : Nat → BitVec 32} (setup : trace.rom = Verification.subwordTable program)
    (ramDomain : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial)
    {w : Nat → ZMod p} (member : (⟨.subwordMemory, w⟩ : Row p TraceKind) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (store byte signed : Bool) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = rowInstruction store byte signed imm rs1 rs2 rd)
    {before after : State} {events : List _root_.MemoryAccess}
    (past : Trace.Proofs.SailHistory cells events initial before)
    (history : Trace.Proofs.SailHistory cells (nativeEvents trace.memoryEpoch w).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause)
        (Trace.Proofs.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (Trace.Proofs.retiredState after (⟨(w 13).val, (w 14).val⟩ : Word).toBitVec) := by
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  rw [setup] at h
  have shape := row_decoder_shape store byte signed imm rs1 rs2 rd encoding fields
  have flags := decoder_selectors limbField h (decoder_field_bounds fields).2.1 query
  have selected : w 10 = if store then 1 else 0 := by
    have flag := flags 0
    cases store <;> cases byte <;> cases signed <;>
      simpa [shape, rowData, importedConstraintsDecoderColumns, Nat.testBit] using flag
  have bounds := (native_value_bounds hp inverse accepted clocks (Trace.Proofs.image_bounds image) setup).1 _ member
  have address := native_address hp inverse accepted clocks image setup member fields query store selected
  have addressCode := (ram_cell clockField inverse accepted clocks image member store selected).2
  apply local_execution hp inverse h (accepted.active _ member) trace.memoryEpoch ordinary fields query
    store byte signed imm rs1 rs2 rd encoding selected
    (by simpa [Row.ports] using bounds) address addressCode (Trace.Proofs.history_configuration past configuration)
    ?_ history
  intro cell bound inside present
  have outside := ramDomain cell.toBitVec present
  rw [Word.toBitVec_toNat bound] at outside
  have low := bound.1
  dsimp [ROM.limit, Word.value, limbBase] at outside low
  omega

end Airbender.SubwordMemory.Proofs

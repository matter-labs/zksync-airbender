import Slop.UnifiedReduced.TriAdd
import Slop.UnifiedReduced.CustomHistory
import Slop.UnifiedReduced.RegisterReads
import Slop.UnifiedReduced.Retirement

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

theorem triadd_metadata {entry : ProgramEntry} {input : TriAdd.Input}
    (fields : customDecoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = .ZIMOP_MOP_RR (4, input.rs2, input.rs1, input.rd)) :
    entry.data = ⟨.machine, (match input.rs1 with | .Regidx bits => bits),
      (match input.rs2 with | .Regidx bits => bits), (match input.rd with | .Regidx bits => bits),
      ⟨0, 0⟩, 512, 0⟩ ∧ input.rd ≠ zeroRegister := by
  rcases input with ⟨left, right, old, ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, pc, before⟩
  rw [encoding] at fields
  by_cases zero : rd = 0
  · simp [customDecoderFields, zero] at fields
  · constructor
    · have result : rd ≠ (0 : BitVec 5) ∧ entry.data =
          ⟨.machine, rs1, rs2, rd, ⟨0, 0⟩, 512, 0⟩ := by
        simpa [customDecoderFields] using fields.symm
      exact result.2
    · simpa [zeroRegister] using zero

theorem triadd_old_read [Fact p.Prime] (hp : limbBase < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {entry : ProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (noStore : w 29 = 0) (query : decoderQuery w = entry.query)
    {cells : List Cell} (epoch : Nat) {before after : State}
    (history : SailHistory cells
      (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rd)) before =
      .ok (TriAdd.oldDestination w).toBitVec before := by
  have indices := native_query_indices hp query
  have low := Verification.assertion_of_holds h ⟨31, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨32, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, noStore] at low high
  have location : w 44 = w 7 := by linear_combination low
  have upper : w 45 = 0 := by linear_combination high
  have read := native_history_read epoch (columns := importedConstraintsTraceColumns)
    (ports := importedConstraintsMemoryPorts) rfl rfl rfl history
    (port := importedConstraintsMemoryPorts[2]) (cell := .register entry.data.rd)
    (by simp [importedConstraintsMemoryPorts]) (by
      simpa [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode,
        noStore, location, upper, pairCode, importedConstraintsDecoderColumns] using
        congrArg (Nat.pair 0) indices.2.2)
  simpa [TriAdd.oldDestination, readToken, MemoryToken.word, importedConstraintsMemoryPorts,
    MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, pairCode, memoryWord, Cell.read] using read

theorem triadd_soundness_from_history [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {cells : List Cell}
    {input : TriAdd.Input} {output : Output} {w : Nat → ZMod p} {after : State} {epoch : Nat}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w importedConstraintsTraceColumns.execute = 1)
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse input.before after)
    (bounds : ∀ i : Fin 3, (readToken w importedConstraintsMemoryPorts[i]).word.Bounded)
    (words : TriAdd.WordMapping input output w)
    {entry : ProgramEntry} (fields : customDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = .ZIMOP_MOP_RR (4, input.rs2, input.rs1, input.rd))
    (pc : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before) :
    TriAdd.spec input output := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have decoderSize : 524288 < p := hp
  have calculationSize : 196608 < p := by omega
  have metadata := triadd_metadata fields encoding
  have flags := decoder_selectors decoderSize core (custom_field_bounds fields).2.1 query
  have selected : w 20 = 1 := by
    have bit := flags 9
    rw [metadata.1] at bit
    simpa [importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using bit
  have noRAM : w 28 = 0 := by
    have bit := flags 17
    rw [metadata.1] at bit
    simpa [importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using bit
  have noStore : w 29 = 0 := by
    have bit := flags 18
    rw [metadata.1] at bit
    simpa [importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using bit
  have l := bounds 0
  have r := bounds 1
  have old := bounds 2
  have leftWord : input.left = ⟨(w 36).val, (w 37).val⟩ := by
    simpa [TriAdd.leftOperand, read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using words.left
  have rightWord : input.right = ⟨(w 42).val, (w 43).val⟩ := by
    simpa [TriAdd.rightOperand, read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using words.right
  have oldWord : input.oldDestination = ⟨(w 48).val, (w 49).val⟩ := by
    simpa [TriAdd.oldDestination, read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using words.oldDestination
  have pcWord : input.pc = Control.initialPC w := words.pc
  have pcValue := native_query_pc_word limbSize query
  change Control.initialPC w = Word.ofBitVec entry.pc at pcValue
  have registers := register_reads limbSize core noRAM query epoch history
  have oldRead := triadd_old_read limbSize core noStore query epoch history
  have rs1 : (.Regidx entry.data.rs1 : SailRV32.regidx) = input.rs1 := by
    rw [metadata.1]
  have rs2 : (.Regidx entry.data.rs2 : SailRV32.regidx) = input.rs2 := by
    rw [metadata.1]
  have rd : (.Regidx entry.data.rd : SailRV32.regidx) = input.rd := by
    rw [metadata.1]
  rw [rs1, rs2, ← leftWord, ← rightWord] at registers
  rw [rd, ← words.oldDestination] at oldRead
  have oldMapping : TriAdd.Calculation.WordMapping input output w := by
    constructor
    · intro _
      repeat' apply And.intro
      all_goals first
        | (rw [leftWord]; exact (ZMod.natCast_zmod_val _).symm)
        | (rw [rightWord]; exact (ZMod.natCast_zmod_val _).symm)
        | (rw [oldWord]; exact (ZMod.natCast_zmod_val _).symm)
    · have index := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query
      change w 7 = (entry.data.rd.toNat : ZMod p) at index
      rw [metadata.1] at index
      cases actual : input.rd with
      | Regidx bits =>
        change w 7 = (bits.toNat : ZMod p)
        rw [actual] at index
        exact index
    · rw [pcWord]; exact (ZMod.natCast_zmod_val _).symm
    · exact congrArg Word.hi pcWord
    · exact congrArg Word.lo words.destination
    · exact congrArg Word.hi words.destination
    · exact congrArg Word.lo words.finalPC
    · exact congrArg Word.hi words.finalPC
  have interfaces : TriAdd.Calculation.InterfaceAssumptions input output w := {
    active := active
    selected := by
      simp only [metadata.2, if_false]
      change w 20 = 1
      exact selected
    ranges := fun _ => ⟨words.left.symm ▸ l, words.right.symm ▸ r,
      words.oldDestination.symm ▸ old⟩
    initialPCLoBound := (pcWord.symm ▸ pcValue.symm ▸ Word.ofBitVec_bound entry.pc).1
    registers := ⟨⟨input.left.toBitVec, registers.1, fun _ => rfl⟩,
      ⟨input.right.toBitVec, registers.2, fun _ => rfl⟩,
      ⟨input.oldDestination.toBitVec, oldRead, fun _ => rfl⟩, pc⟩ }
  exact triadd_soundness calculationSize setup input output w ⟨interfaces, core, oldMapping⟩


theorem triadd_soundness_from_memory [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (inputs : NativeInputs projection trace initial cells program) (accepted : Accepted trace)
    (memory : MemoryExecution trace initial cells)
    {input : TriAdd.Input} {output : Output} {w : Nat → ZMod p}
    (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    (words : TriAdd.WordMapping input output w)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    {entry : ProgramEntry} (fields : customDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = .ZIMOP_MOP_RR (4, input.rs2, input.rs1, input.rd)) :
    TriAdd.spec input output := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  obtain ⟨events, after, past, history⟩ := row_position_from_memory hp inverse accepted
    inputs.clocks memory position
  have ranges := (value_bounds hp inverse accepted inputs.clocks inputs.image).1 _ member
  have bounds (i : Fin 3) := ranges importedConstraintsMemoryPorts[i]
    (by fin_cases i <;> simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  have pc : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before := by
    obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := position
    rw [state, words.pc]
    exact retired_state_pc middle _
  exact triadd_soundness_from_history (by dsimp [timestampBase] at hp; omega)
    core (accepted.active _ member) history bounds words fields query encoding pc

theorem native_triadd_soundness [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    (TriAdd.circuitModel trace initial cells program).SoundnessUnder
      (TriAdd.InterfaceAssumptions trace initial cells program) TriAdd.spec := by
  rintro input output w ⟨assumptions, ⟨accepted, decoded, member⟩, mapping⟩
  obtain ⟨addresses, image⟩ := assumptions.initialization.programImage
  obtain ⟨entry, present, query, encoding⟩ := mapping.instruction
  exact triadd_soundness_from_memory hp inverse assumptions.initialization accepted
    (custom_memory_execution hp inverse accepted assumptions.initialization decoded) member
    mapping.words mapping.state (run_program_sources image entry present).fields query encoding

theorem triadd_execution_from_memory [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (accepted : Accepted trace)
    (inputs : NativeInputs projection trace initial cells program)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : TriAdd.Input} {entry : ProgramEntry}
    (words : TriAdd.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (fields : customDecoderFields entry.instruction = some entry.data)
    (memory : MemoryExecution trace initial cells) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = .ZIMOP_MOP_RR (4, input.rs2, input.rs1, input.rd))
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    run (normalStep (TriAdd.execution input)) (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have result := triadd_soundness_from_memory hp inverse inputs accepted memory member
    words position fields query encoding
  have metadata := triadd_metadata fields encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have destination : (.Regidx entry.data.rd : SailRV32.regidx) = input.rd := by rw [metadata.1]
  change stepSpec input.before (TriAdd.execution input) input.rd
    ⟨Control.destination w, Control.finalPC w⟩ at result
  rw [atRow] at result
  exact custom_register_retirement (by dsimp [timestampBase] at hp; omega)
    core fields query destination trace.memoryEpoch history result

theorem triadd_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (inputs : NativeInputs customDecoderFields trace initial cells program)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : TriAdd.Input} {entry : ProgramEntry}
    (words : TriAdd.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = .ZIMOP_MOP_RR (4, input.rs2, input.rs1, input.rd))
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    run (normalStep (TriAdd.execution input)) (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  obtain ⟨addresses, image⟩ := inputs.programImage
  exact triadd_execution_from_memory hp inverse accepted inputs member words atRow position
    (run_program_sources image entry present).fields
    (custom_memory_execution hp inverse accepted inputs decoded) query encoding history

end Airbender.UnifiedReduced.Proofs

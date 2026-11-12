module
public import Human.Trace.Families.MulDiv.RVTheorems
public import Proven.MulDiv.RVQuery
public import Proven.MulDiv.RVResult
public import Proven.MulDiv.Values
public import Proven.Trace.RVFamilyTrace
public import Proven.Trace.RVValues
public import Proven.Trace.RVZeroRows
public import Proven.Defs.Helpers.Memory.Ports
public import Proven.Defs.Helpers.Decoder.RVProgram
public import Proven.Defs.Helpers.Memory.RowEvents
public import Proven.Defs.Helpers.Memory.History
public import Proven.Defs.Circuits.MulDiv.Operation
public import Proven.Defs.Helpers.Core.Word

@[expose] public section

/-! The MulDiv trace claim on the RV route (`RVTraceSoundnessClaim`): no Sail state, interpreter or `Configured` fact.
    Each row is one `RV.exec` of its entry's instruction (`rv_row_step`: decoder facts `rv_query_facts`, operand
    registers and destination update from the row's RV history `rv_register_ports`, result `rv_row_result`, PC
    `pc_successor`); x0 is preserved (`mulDiv_row_zero_preserving`); the composition is `rv_family_realizes`. -/

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace Trace.Proofs

/-- A successful projection is the data of an RV input of this family. -/
theorem rv_fields_input {i : RV.Instr} {d : DecoderData Unit} (fields : rvDecoderFields i = some d)
    (s : RV.State) :
    ∃ input : RVInput, input.before = s ∧ i = rvInstruction input ∧ d = rvData input := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals rename_i rd rs1 rs2
  all_goals try cases fields
  all_goals by_cases hz : rd = 0
  all_goals simp only [hz, ite_true, ite_false, reduceCtorEq] at fields
  case neg =>
    obtain rfl := Option.some.inj fields
    exact ⟨⟨.mul, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, s⟩, rfl, rfl, rfl⟩
  case neg =>
    obtain rfl := Option.some.inj fields
    exact ⟨⟨.mulhu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, s⟩, rfl, rfl, rfl⟩
  case neg =>
    obtain rfl := Option.some.inj fields
    exact ⟨⟨.divu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, s⟩, rfl, rfl, rfl⟩
  case neg =>
    obtain rfl := Option.some.inj fields
    exact ⟨⟨.remu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, s⟩, rfl, rfl, rfl⟩

/-- Read, write and terminal values of an accepted trace seeded by an RV image are bounded words. -/
theorem rv_value_bounds {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded :=
  read_bounds_of_sources hp inverse accepted clocks (RVValues.rv_image_bounds image) (write_sources accepted)

/-- Every row of an accepted RV-decoded trace preserves x0. -/
theorem rv_zero_preserving {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : NativeTrace p} {initial : RV.State} {addresses : List (BitVec 32)} {program : List RVProgramEntry}
    (image : rvProgramImageWith rvDecoderFields initial addresses = some program)
    (decoded : RVDecoded trace program) : ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, present, _, query⟩ := rv_decoder_member (decoded row member)
  obtain ⟨_, _, i, _, fields⟩ := rvProgram_entry_fetch image entry present
  exact RVZero.mulDiv_row_zero_preserving hp row entry fields query

/-- One MulDiv row is one `RV.exec` of its entry's instruction, agreeing with the row's RV history and final PC. -/
theorem rv_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    {entry : RVProgramEntry} (query : decoderQuery w = entry.query)
    {i : RV.Instr} (fields : rvDecoderFields i = some entry.data)
    (leftBound : (Word.mk (w 20).val (w 21).val).Bounded)
    {cells : List Cell} (epoch : Nat) {before after : RV.State} (pc : before.pc = entry.pc)
    (history : RVHistory cells (rowEvents epoch (⟨.mulDiv, w⟩ : Row p TraceKind)).reverse before after) :
    ∃ next, RV.exec before i = some next ∧
      RV.Same next { after with pc := (⟨.mulDiv, w⟩ : Row p TraceKind).finish.word.toBitVec } := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨input, rfl, rfl, data⟩ := rv_fields_input fields before
  let pooled : RVPooledProgramEntry := entry.mapFamily (fun _ => .mulDiv)
  have pooledData : pooled.data = (rvData input).mapFamily (fun _ => .mulDiv) := by
    simp only [pooled, RVProgramEntry.mapFamily, data]
  obtain ⟨selected, pcWord, rs1Query, rs2Query, rdQuery⟩ :=
    rv_query_facts hp core pooledData (p := p) (w := w) query
  change _ = Word.ofBitVec entry.pc at pcWord
  -- Operand registers and destination update, from the row's RV history.
  have index {column : Nat} {k : BitVec 5} (equal : w column = (k.toNat : ZMod p)) :
      (w column).val = k.toNat := by
    rw [equal, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := k.isLt; omega)]
  have shaped : RVHistory cells (nativeRowEvents epoch importedConstraintsTraceColumns
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1], importedConstraintsMemoryPorts[2]]
      w).reverse input.before after := history
  obtain ⟨left, right, written⟩ := rv_register_ports epoch (by simp [importedConstraintsMemoryPorts])
    (by simp [importedConstraintsMemoryPorts]) (a := 5) (b := 6) (c := 7)
    (by simp [importedConstraintsMemoryPorts]) (by simp [importedConstraintsMemoryPorts])
    (by simp [importedConstraintsMemoryPorts]) (index rs1Query) (index rs2Query) (index rdQuery) shaped
  have leftWord : memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) =
      (Word.mk (w 20).val (w 21).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have rightWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 24).val (w 25).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have destinationWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 28).val (w 29).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  rw [leftWord] at left
  rw [rightWord] at right
  rw [destinationWord] at written
  -- The row calculation and the PC.
  have result := rv_row_result hp inverse core input.operation selected leftBound
  have pcBound : (Word.mk (w 0).val (w 1).val).Bounded := by
    rw [pcWord]; exact Word.ofBitVec_bound entry.pc
  have pcNext := pc_successor (by omega) inverse core (initial := Word.mk (w 0).val (w 1).val)
    (final := Word.mk (w 14).val (w 15).val)
    ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ pcBound
  have finalPC : (⟨.mulDiv, w⟩ : Row p TraceKind).finish.word.toBitVec = input.before.pc + 4 := by
    change (Word.mk (w 14).val (w 15).val).toBitVec = _
    rw [pcNext.2.2, pcWord, Word.ofBitVec_roundtrip, pc]
  have exec : RV.exec input.before (rvInstruction input) = some (input.before.setReg input.rd
      (RV.alu input.operation.rvOp (input.before.getReg input.rs1) (input.before.getReg input.rs2))).nextInstr := by
    cases hop : input.operation <;> simp [rvInstruction, hop, Operation.rvOp, RV.exec]
  refine ⟨_, exec, rv_same_next ?_ finalPC⟩
  rw [left, right, ← result]
  exact written

/-- `MulDiv.RVTraceSoundnessClaim`, proved. -/
theorem rv_trace_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry}
    (inputs : RVExecutionInputs trace initial cells program)
    (accepted : Accepted trace) (decoded : RVDecoded trace program) :
    RVRealizes trace initial cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, image⟩ := inputs.programImage
  have bounds := rv_value_bounds clockSize clockInverse accepted inputs.clocks inputs.image
  refine rv_family_realizes clockSize clockInverse accepted inputs (rv_zero_preserving limbSize image decoded)
    (rv_family_row_steps limbSize image (fun _ _ => True)
      (fun row member => by
        obtain ⟨entry, present, _, query⟩ := rv_decoder_member (decoded row member)
        exact ⟨entry, present, trivial, query⟩) ?_)
  intro row member entry _ _ query i _ fields _ before after pc _ history
  obtain ⟨family, w⟩ := row
  cases family
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have left := bounds _ member importedConstraintsMemoryPorts[0]
    (by change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
  have leftBound : (Word.mk (w 20).val (w 21).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using left
  exact rv_row_step hp inverse core query fields leftBound trace.memoryEpoch pc history

end Airbender.MulDiv.Proofs

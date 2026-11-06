import Human.Circuits.MulDiv.RVTheorems
import Slop.MulDiv.RVQuery
import Slop.MulDiv.RVResult
import Slop.Trace.RVValues
import Slop.Trace.RVPooledRow
import Slop.Trace.RVRowGlue

/-! RV32 MulDiv soundness (`RVSoundnessClaim`), on the RV route: no Sail state, interpreter or `Configured` fact.

    - Fetch/step: the row's program entry is an aligned ROM word of the starting memory (`rvProgram_entry_fetch`);
      the row's pre-state has the entry's PC and the starting ROM bytes, so `RV.step` executes `rvInstruction input`.
    - Decoder: the entry's data is `rvData input` (`rv_pooled_fields`, which also gives `rd ≠ x0`); the query fixes
      selectors, PC limbs and register indices (`rv_query_facts`).
    - Operands: the row's two read ports hold the pre-state registers `rs1`, `rs2` (`rv_row_operand_reads`); the left
      operand's limbs are bounded (`rv_pooled_value_bounds`).
    - Result: `rv_row_result` (row calculation = `RV.alu`). PC: `pc_successor`. -/

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace Trace.Proofs

/-- The pre-state registers `i`, `j` are the values the row's first two ports read. -/
theorem rv_muldiv_row_operands (laws : RVPooledLaws) {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    (assumptions : RVInterfaceAssumptions trace initial cells program)
    (decoded : RVPooledDecoded trace program)
    {w : Nat → ZMod p}
    {before : RV.State} (position : RVRowPosition trace initial cells (⟨.mulDiv, w⟩ : Row p PooledFamily) before) :
    ∀ i j : BitVec 5, w 5 = (i.toNat : ZMod p) → w 6 = (j.toNat : ZMod p) →
      before.getReg i = (Word.mk (w 20).val (w 21).val).toBitVec ∧
      before.getReg j = (Word.mk (w 24).val (w 25).val).toBitVec := by
  intro i j hi hj
  have shape : (⟨.mulDiv, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.mulDiv, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := rfl
    rw [portsEq]
    first
      | rfl
      | simp [importedConstraintsMemoryPorts]
  have operands := rv_row_register_reads laws hp inverse accepted assumptions decoded position shape
    (by simp [importedConstraintsMemoryPorts]) (a := 5) (b := 6)
    (by first | rfl | simp [importedConstraintsMemoryPorts])
    (by first | rfl | simp [importedConstraintsMemoryPorts]) hi hj
  have leftWord : memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) =
      (Word.mk (w 20).val (w 21).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have rightWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 24).val (w 25).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  exact ⟨operands.1.trans leftWord, operands.2.trans rightWord⟩

theorem rv_trace_soundness (laws : RVPooledLaws) : RVSoundnessClaim := by
  intro p _ hp inverse trace initial cells program assumptions input output w relation
  obtain ⟨⟨accepted, decoded, member⟩, mapping⟩ := relation
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints) importedConstraintsTimestampLookups)
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  -- The row's program entry: its bytes decode to the row's instruction, and its data is `rvData input`.
  obtain ⟨entry, present, _, query, decodes⟩ := mapping.instruction
  obtain ⟨guard, bits, i, decodedI, projection⟩ := rvProgram_entry_fetch programImage entry present
  have hi : i = rvInstruction input := Option.some.inj (decodedI.symm.trans decodes)
  subst hi
  obtain ⟨_, data⟩ := rv_pooled_fields projection
  obtain ⟨selected, pcWord, rs1Query, rs2Query, _⟩ := rv_query_facts hp core data query
  -- Fetch/step: the row's pre-state is at the entry's PC and executes the entry's instruction.
  obtain ⟨beforePC, step⟩ := rv_step_of_position mapping.state (rv_query_pc limbSize query) guard
    (by rw [← bits]; exact decodes)
  -- PC successor.
  have rowPC : input.pc = Word.mk (w 0).val (w 1).val :=
    congrArg₂ Word.mk mapping.words.pcLo mapping.words.pcHi
  have pcBounds : input.pc.Bounded := by
    rw [rowPC, pcWord]
    exact Word.ofBitVec_bound entry.pc
  have pcNext := pc_successor (by omega) arithmeticInverse core
    ⟨by rw [rowPC]; exact (ZMod.natCast_zmod_val _).symm,
     by rw [rowPC]; exact (ZMod.natCast_zmod_val _).symm,
     mapping.words.finalPCLo, mapping.words.finalPCHi⟩ pcBounds
  have hpc : input.before.pc + 4 = output.pc.toBitVec := by
    rw [pcNext.2.2, rowPC, pcWord, Word.ofBitVec_roundtrip, beforePC]
  -- Left operand bound.
  have readBounds := (laws.valueBounds (by omega) inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image
    assumptions.wordTable assumptions.subwordTable programImage decoded).1 _ member
  have left := readBounds importedConstraintsMemoryPorts[0]
    (by change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
  have leftBound : (Word.mk (w 20).val (w 21).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using left
  -- Operand registers and the row calculation.
  have regs := rv_muldiv_row_operands laws clockSize inverse accepted assumptions decoded mapping.state
    input.rs1 input.rs2 rs1Query rs2Query
  have result := rv_row_result hp arithmeticInverse core input.operation selected leftBound
  have destination : output.destination = Word.mk (w 28).val (w 29).val :=
    congrArg₂ Word.mk mapping.words.outputLo mapping.words.outputHi
  have value : RV.alu input.operation.rvOp (input.before.getReg input.rs1) (input.before.getReg input.rs2) =
      output.destination.toBitVec := by
    rw [regs.1, regs.2, destination, result]
  refine ⟨(input.before.setReg input.rd
      (RV.alu input.operation.rvOp (input.before.getReg input.rs1) (input.before.getReg input.rs2))).nextInstr,
    ?_, rv_same_of_write _ _ _ _ _ (fun _ => value) hpc⟩
  rw [step]
  cases hop : input.operation <;> simp [rvInstruction, hop, Operation.rvOp, RV.exec]

theorem babyBear_rv_trace_soundness (laws : RVPooledLaws) : BabyBearRVSoundnessClaim := by
  intro trace initial cells program assumptions input output w relation
  exact rv_trace_soundness laws (p := babyBearModulus) (by decide) (by decide) trace initial cells program
    assumptions input output w relation

end Airbender.MulDiv.Proofs

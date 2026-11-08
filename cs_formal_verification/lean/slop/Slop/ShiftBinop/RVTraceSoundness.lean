module
public import Human.Circuits.ShiftBinop.RVTheorems
public import Slop.ShiftBinop.RVQuery
public import Slop.ShiftBinop.RVResult
public import Slop.Trace.RVPooledRow
public import Slop.Trace.RVZero
public import Slop.Trace.RVRowGlue

@[expose] public section

/-! RV32 shift/binop soundness (`RVSoundnessClaim`), on the RV route: no Sail state, interpreter or `Configured`
    fact.

    - Fetch/step: the row's program entry is an aligned ROM word of the starting memory (`rvProgram_entry_fetch`);
      the row's pre-state has the entry's PC and the starting ROM bytes, so `RV.step` executes `rvInstruction input`.
    - Decoder: the entry's data is `rvData input` (`rv_pooled_fields_family`, `rv_fields`); the query fixes selectors,
      tag, immediate columns, PC limbs and register indices (`rv_query_facts`).
    - Operands: the row's two read ports hold the pre-state registers `rs1` and the decoded second source
      (`rv_shift_row_operands`); for immediate forms and REV8 that source is x0, read as zero
      (`rv_zero_reads_of_preserving`).
    - Result: `rv_row_value` (row calculation = `RV.alu` / `RV.rev8`). PC: `pc_successor`. -/

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace Trace.Proofs

/-- The pre-state registers `i`, `j` are the values the row's first two ports read. -/
theorem rv_shift_row_operands (laws : RVPooledLaws) {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    (assumptions : RVInterfaceAssumptions trace initial cells program)
    (decoded : RVPooledDecoded trace program)
    {w : Nat → ZMod p}
    {before : RV.State}
    (position : RVRowPosition trace initial cells (⟨.shiftBinop, w⟩ : Row p PooledFamily) before) :
    ∀ i j : BitVec 5, w 5 = (i.toNat : ZMod p) → w 6 = (j.toNat : ZMod p) →
      before.getReg i = memoryWord (importedConstraintsMemoryPorts[0].readCode w) ∧
      before.getReg j = memoryWord (importedConstraintsMemoryPorts[1].readCode w) := by
  intro i j hi hj
  have shape : (⟨.shiftBinop, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.shiftBinop, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := by rfl
    rw [portsEq]
    rfl
  have operands := rv_row_register_reads laws hp inverse accepted assumptions decoded position shape
    (by simp [importedConstraintsMemoryPorts]) (a := 5) (b := 6)
    (by first | rfl | simp [importedConstraintsMemoryPorts])
    (by first | rfl | simp [importedConstraintsMemoryPorts]) hi hj
  exact operands

/-- For immediate forms and REV8 the second port reads x0 (`w 6 = 0`): its read is zero. -/
theorem rv_shift_zero_read (laws : RVPooledLaws) {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    (assumptions : RVInterfaceAssumptions trace initial cells program)
    (decoded : RVPooledDecoded trace program)
    {w : Nat → ZMod p} (member : (⟨.shiftBinop, w⟩ : Row p PooledFamily) ∈ trace.rows)
    (zero : w 6 = 0) : importedConstraintsMemoryPorts[1].readCode w = 0 := by
  haveI : ClockLaws PooledFamily p := laws.clockLaws
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  have reads := Airbender.Trace.RVZero.rv_zero_reads_of_preserving hp inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image
    (laws.zeroPreserving (by dsimp [timestampBase] at hp; omega)
      accepted programImage decoded)
  have present : importedConstraintsMemoryPorts[1] ∈ (⟨.shiftBinop, w⟩ : Row p PooledFamily).ports := by
    change importedConstraintsMemoryPorts[1] ∈ importedConstraintsMemoryPorts
    simp [importedConstraintsMemoryPorts]
  have atZero : (importedConstraintsMemoryPorts[1]).address.code w = (Cell.register 0).addressCode := by
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, zero]
  exact reads _ member _ present atZero

/-- For immediate forms and REV8 the second source does not matter. -/
theorem rv_value_second {operation : Operation} {immediate : Bool} (imm : BitVec 12) (x y y' : BitVec 32)
    (ignored : (immediate || operation = .rev8) = true) :
    rvValue operation immediate imm x y = rvValue operation immediate imm x y' := by
  cases operation <;> cases immediate <;> simp_all [rvValue, rvOperand]

/-- `RV.exec` of the row's instruction writes `rvValue` of the source registers to `rd`. -/
theorem rv_exec_row (s : RV.State) (input : RVInput) :
    RV.exec s (rvInstruction input) = some (s.setReg input.rd
      (rvValue input.operation input.immediate input.encodedImmediate (s.getReg input.rs1)
        (s.getReg input.rs2))).nextInstr := by
  obtain ⟨operation, immediate, left, right, pc, rs1, rs2, rd, imm, before⟩ := input
  cases operation <;> cases immediate <;>
    simp [rvInstruction, RV.exec, rvValue, rvOperand, Operation.rvOp, Operation.isShift]

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
  obtain ⟨entry, present, family, query, decodes⟩ := mapping.instruction
  obtain ⟨guard, bits, i, decodedI, projection⟩ := rvProgram_entry_fetch programImage entry present
  have hi : i = rvInstruction input := Option.some.inj (decodedI.symm.trans decodes)
  subst hi
  obtain ⟨d, fields, data⟩ := (rv_pooled_fields_family projection).2.2.2.1 family
  rw [rv_fields fields] at data
  obtain ⟨selected, funct3, immediateLo, immediateHi, pcWord, rs1Query, rs2Query, _⟩ :=
    rv_query_facts hp core data query
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
  -- Operand registers (x0 for immediate forms and REV8) and the row calculation.
  have zeroRead : (input.immediate || input.operation = .rev8) = true →
      importedConstraintsMemoryPorts[1].readCode w = 0 := by
    intro ignored
    exact rv_shift_zero_read laws clockSize inverse accepted assumptions decoded member
      (by simpa [ignored] using rs2Query)
  have regs := rv_shift_row_operands laws clockSize inverse accepted assumptions decoded mapping.state
    _ _ rs1Query rs2Query
  have result := rv_row_value (by omega) core input.operation input.immediate input.encodedImmediate
    selected funct3 immediateLo immediateHi zeroRead
  have destination : output.destination = Word.mk (w 31).val (w 32).val :=
    congrArg₂ Word.mk mapping.words.outputLo mapping.words.outputHi
  have value : rvValue input.operation input.immediate input.encodedImmediate
      (input.before.getReg input.rs1) (input.before.getReg input.rs2) = output.destination.toBitVec := by
    rw [destination, result, regs.1, ← regs.2]
    by_cases ignored : (input.immediate || input.operation = .rev8) = true
    · exact rv_value_second _ _ _ _ ignored
    · split
      · contradiction
      · rfl
  refine ⟨_, step.trans (rv_exec_row _ _), rv_same_of_write _ _ _ _ _ (fun _ => value) hpc⟩

theorem babyBear_rv_trace_soundness (laws : RVPooledLaws) : BabyBearRVSoundnessClaim := by
  intro trace initial cells program assumptions input output w relation
  exact rv_trace_soundness laws (p := babyBearModulus) (by decide) (by decide) trace initial cells program
    assumptions input output w relation

end Airbender.ShiftBinop.Proofs

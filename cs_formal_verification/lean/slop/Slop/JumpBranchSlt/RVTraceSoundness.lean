module
public import Human.Circuits.JumpBranchSlt.RVTheorems
public import Slop.JumpBranchSlt.RVRow
public import Slop.Trace.RVPooledRow
public import Slop.Trace.RVValues
public import Slop.Trace.PC
public import Slop.Trace.RVRowGlue

@[expose] public section

/-! RV32 comparison, branch and jump soundness (`Comparison/Branch/Jump.RVSoundnessClaim`), on the RV route: no Sail
    state, interpreter or `Configured` fact.

    - Fetch/step: the row's program entry is an aligned ROM word of the starting memory (`rvProgram_entry_fetch`)
      that decodes to `rvInstruction input`; the row's pre-state has the entry's PC, so `RV.step` executes it
      (`rv_step_of_position`). Its native data is `comparisonData`/`branchData`/`jumpData`.
    - Row facts (`RVRowFacts`, `rv_row_facts`): selectors, immediate and tag from the decoder query, operand values
      from the row's RV history (`rv_pooled_row_history`), operand bounds (`rv_pooled_value_bounds`), and the
      outgoing PC's high limb from PC matching: the next row's decoder-table PC or the terminal PC (`terminalPC`; the
      circuit does not range-check column 17).
    - Row calculation: `rv_comparison_exec`, `rv_branch_exec`, `rv_jump_exec`. -/

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Trace.Proofs

/-- Every outgoing PC of an RV-decoded pooled trace is canonical when the terminal PC is (as `pooled_pc_bounds`). -/
theorem rv_pooled_finish_bounds {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : PooledTrace p} (accepted : Accepted trace) {program : List RVPooledProgramEntry}
    (decoded : RVPooledDecoded trace program) (terminal : trace.terminal.word.Bounded) :
    ∀ row ∈ trace.rows, row.finish.word.Bounded := by
  have incoming : ∀ row ∈ trace.rows, row.start.word.Bounded := by
    intro row member
    obtain ⟨entry, _, _, query⟩ := rv_decoder_member (decoded row member)
    have canonical := rv_native_query_pc_word hp query
    change row.start.word = Word.ofBitVec entry.pc at canonical
    exact canonical.symm ▸ Word.ofBitVec_bound entry.pc
  exact outgoing_pc_bounds accepted incoming terminal

/-- The two operand registers of a JumpBranchSlt row hold the values the row read (as `rv_addsub_row_position`). -/
theorem rv_jbs_row_reads (laws : RVPooledLaws) {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    (inputs : RVPooledHistoryInputs trace initial cells program)
    (decoded : RVPooledDecoded trace program)
    {w : Nat → ZMod p} {before : RV.State}
    (position : RVRowPosition trace initial cells (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) before) :
    ∀ i j : BitVec 5, w 5 = (i.toNat : ZMod p) → w 6 = (j.toNat : ZMod p) →
      before.getReg i = (Word.mk (w 22).val (w 23).val).toBitVec ∧
      before.getReg j = (Word.mk (w 26).val (w 27).val).toBitVec := by
  intro i j hi hj
  have shape : (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := by rfl
    rw [portsEq]
    rfl
  have operands := rv_row_register_reads laws hp inverse accepted inputs decoded position shape
    (by simp [importedConstraintsMemoryPorts]) (a := 5) (b := 6)
    rfl
    rfl hi hj
  have leftWord : memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) =
      (Word.mk (w 22).val (w 23).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have rightWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 26).val (w 27).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  exact ⟨operands.1.trans leftWord, operands.2.trans rightWord⟩

/-- Everything the row calculation needs, from the trace: the row's facts at its RV pre-state, and `RV.step` of that
    pre-state is `RV.exec` of the instruction its program entry decodes to. -/
theorem rv_row_facts (laws : RVPooledLaws) {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    (assumptions : RVTraceInputs trace initial cells program) (accepted : Accepted trace)
    (decoded : RVPooledDecoded trace program) {w : Nat → ZMod p}
    (member : (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows) {before : RV.State}
    (position : RVRowPosition trace initial cells ⟨.jumpBranchSlt, w⟩ before)
    {entry : RVPooledProgramEntry} (present : entry ∈ program) (family : entry.data.family = .jumpBranchSlt)
    (query : (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).decoderQuery = entry.query)
    {i : RV.Instr} (decodes : RV.decode entry.bits = some i) {data : DecoderData Unit}
    (fields : ∀ d, rvPooledDecoderFields i = some d → d.family = .jumpBranchSlt →
      d = data.mapFamily (fun _ => .jumpBranchSlt))
    (small : data.mask < 32) :
    RVRowFacts w before data ∧ RV.step before = RV.exec before i := by
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  obtain ⟨guard, bits, i', decodedI, projection⟩ := rvProgram_entry_fetch programImage entry present
  have hi : i' = i := Option.some.inj (decodedI.symm.trans decodes)
  subst hi
  have dataEq := fields _ projection family
  obtain ⟨pc, entryBits, entryData⟩ := entry
  change entryData = data.mapFamily (fun _ => .jumpBranchSlt) at dataEq
  subst dataEq
  change entryBits = RV.read initial.rom pc 4 at bits
  change pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0 at guard
  change RV.decode entryBits = some i' at decodedI
  have query0 : decoderQuery w = (⟨pc, entryBits, data⟩ : JumpBranchSlt.RVProgramEntry).query := query
  obtain ⟨beforePC, step⟩ := rv_step_of_position position (rv_query_pc limbSize query) guard
    (by rw [← bits]; exact decodedI)
  change before.pc = pc at beforePC
  refine ⟨?_, step⟩
  have pcWord := rv_native_query_pc_word limbSize query0
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec pc at pcWord
  rw [← beforePC] at pcWord guard
  have rs1Query := congrArg (fun q : Vector (ZMod p) 9 => q[2]) query0
  change w 5 = (data.rs1.toNat : ZMod p) at rs1Query
  have rs2Query := congrArg (fun q : Vector (ZMod p) 9 => q[3]) query0
  change w 6 = (data.rs2.toNat : ZMod p) at rs2Query
  have regs := rv_jbs_row_reads laws clockSize inverse accepted assumptions.toRVPooledHistoryInputs decoded
    position data.rs1 data.rs2 rs1Query rs2Query
  have readBounds := (laws.valueBounds (by omega) inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image
    assumptions.wordTable assumptions.subwordTable programImage decoded).1 _ member
  have left := readBounds importedConstraintsMemoryPorts[0]
    (by change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
  have right := readBounds importedConstraintsMemoryPorts[1]
    (by change importedConstraintsMemoryPorts[1] ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
  have bounds : (Word.mk (w 22).val (w 23).val).Bounded ∧
      (Word.mk (w 26).val (w 27).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using And.intro left right
  have finish := rv_pooled_finish_bounds limbSize accepted decoded assumptions.terminalPC _ member
  change (Word.mk (w 16).val (w 17).val).Bounded at finish
  have flags := rv_decoder_selectors limbSize h small query0
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query0
  change w 8 = (data.immediate.lo : ZMod p) at low
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query0
  change w 9 = (data.immediate.hi : ZMod p) at high
  have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query0
  change w 10 = (data.funct3 : ZMod p) at tag
  refine ⟨h, pcWord, guard.2, low, high, tag, ?_, regs.1, regs.2, bounds.1, bounds.2, finish.2⟩
  intro k
  have flag := flags k
  fin_cases k <;> simpa [importedConstraintsDecoderColumns] using flag

theorem rv_comparison_trace_soundness (laws : RVPooledLaws) : Comparison.RVSoundnessClaim := by
  intro p _ hp inverse trace initial cells program assumptions input output w relation
  obtain ⟨⟨accepted, decoded, member⟩, mapping⟩ := relation
  obtain ⟨entry, present, family, query, decodes⟩ := mapping.instruction
  obtain ⟨facts, step⟩ := rv_row_facts laws hp inverse assumptions accepted decoded member mapping.state present family
    query decodes (fun _ fields family => comparison_pooled_fields fields family)
    (by unfold comparisonData; split <;> simp)
  obtain ⟨s', exec, same⟩ := rv_comparison_exec (by omega) facts mapping.words.outputLo mapping.words.outputHi
    mapping.words.finalPCLo mapping.words.finalPCHi
  exact ⟨s', step.trans exec, same⟩

theorem rv_branch_trace_soundness (laws : RVPooledLaws) : Branch.RVSoundnessClaim := by
  intro p _ hp inverse trace initial cells program assumptions input output w relation
  obtain ⟨⟨accepted, decoded, member⟩, mapping⟩ := relation
  obtain ⟨entry, present, family, query, decodes⟩ := mapping.instruction
  obtain ⟨facts, step⟩ := rv_row_facts laws hp inverse assumptions accepted decoded member mapping.state present family
    query decodes (fun _ fields family => branch_pooled_fields fields family) (by simp [branchData])
  obtain ⟨s', exec, same⟩ := rv_branch_exec (by omega) facts (decode_branch_even decodes)
    mapping.words.finalPCLo mapping.words.finalPCHi
  exact ⟨s', step.trans exec, same⟩

theorem rv_jump_trace_soundness (laws : RVPooledLaws) : Jump.RVSoundnessClaim := by
  intro p _ hp inverse trace initial cells program assumptions input output w relation
  obtain ⟨⟨accepted, decoded, member⟩, mapping⟩ := relation
  obtain ⟨entry, present, family, query, decodes⟩ := mapping.instruction
  obtain ⟨facts, step⟩ := rv_row_facts laws hp inverse assumptions accepted decoded member mapping.state present family
    query decodes (fun _ fields family => jump_pooled_fields fields family)
    (by unfold jumpData; split <;> split <;> simp)
  have even : ∀ offset, input.instruction = .jal offset → (offset.signExtend 32).toNat % 2 = 0 := by
    intro offset jal
    have d := decodes
    simp only [Jump.rvInstruction, jal] at d
    exact decode_jal_even d
  obtain ⟨s', exec, same⟩ := rv_jump_exec (by omega) facts even mapping.words.outputLo mapping.words.outputHi
    mapping.words.finalPCLo mapping.words.finalPCHi
  exact ⟨s', step.trans exec, same⟩

theorem babyBear_rv_comparison_trace_soundness (laws : RVPooledLaws) : Comparison.BabyBearRVSoundnessClaim := by
  intro trace initial cells program assumptions input output w relation
  exact rv_comparison_trace_soundness laws (p := babyBearModulus) (by decide) (by decide) trace initial cells program
    assumptions input output w relation

theorem babyBear_rv_branch_trace_soundness (laws : RVPooledLaws) : Branch.BabyBearRVSoundnessClaim := by
  intro trace initial cells program assumptions input output w relation
  exact rv_branch_trace_soundness laws (p := babyBearModulus) (by decide) (by decide) trace initial cells program
    assumptions input output w relation

theorem babyBear_rv_jump_trace_soundness (laws : RVPooledLaws) : Jump.BabyBearRVSoundnessClaim := by
  intro trace initial cells program assumptions input output w relation
  exact rv_jump_trace_soundness laws (p := babyBearModulus) (by decide) (by decide) trace initial cells program
    assumptions input output w relation

end Airbender.JumpBranchSlt.Proofs

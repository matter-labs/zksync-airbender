module
public import Human.Trace.Families.JumpBranchSlt.RVTheorems
public import Slop.JumpBranchSlt.RVRow
public import Slop.JumpBranchSlt.RVValues
public import Slop.JumpBranchSlt.Trace
public import Slop.Trace.RVFamilyTrace
public import Slop.Trace.RVValues
public import Slop.Trace.RVZeroRows
public import Slop.Trace.PC
public import Slop.ISA.RV.DecodeShape

@[expose] public section

/-! The comparison/branch/jump trace claim on the RV route (`RVTraceSoundnessClaim`): no Sail state, interpreter or
    `Configured` fact. Each row is one `RV.exec` of its entry's instruction (`rv_row_step`): the row facts
    (`RVRowFacts`: decoder query, operand registers from the row's RV history, operand bounds, the outgoing PC's high
    limb from PC matching and the canonical terminal PC) feed `rv_comparison_exec`, `rv_branch_exec`, `rv_jump_exec`;
    the destination update is the row's history (`rv_register_ports`). x0 is preserved
    (`jumpBranch_row_zero_preserving`); the composition is `rv_family_realizes`. -/

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Trace.Proofs

/-- One JumpBranchSlt row is one `RV.exec` of its entry's instruction, agreeing with the row's RV history and final
    PC. -/
theorem rv_row_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    {entry : RVProgramEntry} (query : decoderQuery w = entry.query)
    {i : RV.Instr} (decodes : RV.decode entry.bits = some i) (fields : rvDecoderFields i = some entry.data)
    (aligned : entry.pc.toNat % 4 = 0)
    (leftBound : (Word.mk (w 22).val (w 23).val).Bounded) (rightBound : (Word.mk (w 26).val (w 27).val).Bounded)
    (finalHi : (w 17).val < limbBase)
    {cells : List Cell} (epoch : Nat) {before after : RV.State} (pc : before.pc = entry.pc)
    (history : RVHistory cells (rowEvents epoch (⟨.jumpBranchSlt, w⟩ : Row p TraceKind)).reverse before after) :
    ∃ next, RV.exec before i = some next ∧
      RV.Same next { after with pc := (⟨.jumpBranchSlt, w⟩ : Row p TraceKind).finish.word.toBitVec } := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have shape := RV.decode_shape decodes
  -- Decoder facts of the entry's data.
  have bounds := rv_decoder_field_bounds fields
  have pcWord := rv_native_query_pc_word limbSize query
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at pcWord
  rw [← pc] at pcWord aligned
  have q (k : Fin 9) := congrArg (fun v : Vector (ZMod p) 9 => v[k]) query
  have low : w 8 = (entry.data.immediate.lo : ZMod p) := q 5
  have high : w 9 = (entry.data.immediate.hi : ZMod p) := q 6
  have tag : w 10 = (entry.data.funct3 : ZMod p) := q 7
  have indices := rv_native_query_indices limbSize query
  change (w 5).val = entry.data.rs1.toNat ∧ (w 6).val = entry.data.rs2.toNat ∧ (w 7).val = entry.data.rd.toNat
    at indices
  have selectors := rv_decoder_selectors limbSize core bounds.2.1 query
  have flags : ∀ k : Fin 5, w (11 + k.val) = if entry.data.mask.testBit k.val then 1 else 0 := by
    intro k
    have flag := selectors k
    fin_cases k <;> simpa [importedConstraintsDecoderColumns] using flag
  -- Operand registers and destination update, from the row's RV history.
  have shaped : RVHistory cells (nativeRowEvents epoch importedConstraintsTraceColumns
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1], importedConstraintsMemoryPorts[2]]
      w).reverse before after := history
  obtain ⟨left, right, written⟩ := rv_register_ports epoch (by simp [importedConstraintsMemoryPorts])
    (by simp [importedConstraintsMemoryPorts]) (a := 5) (b := 6) (c := 7)
    (by simp [importedConstraintsMemoryPorts]) (by simp [importedConstraintsMemoryPorts])
    (by simp [importedConstraintsMemoryPorts]) indices.1 indices.2.1 indices.2.2 shaped
  have leftWord : memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) =
      (Word.mk (w 22).val (w 23).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have rightWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 26).val (w 27).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have destinationWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 30).val (w 31).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  rw [leftWord] at left
  rw [rightWord] at right
  rw [destinationWord] at written
  have facts : RVRowFacts w before entry.data :=
    ⟨core, pcWord, aligned, low, high, tag, flags, left, right, leftBound, rightBound, finalHi⟩
  let output : Circuit.Output := ⟨⟨(w 30).val, (w 31).val⟩, ⟨(w 16).val, (w 17).val⟩⟩
  have finish : (⟨.jumpBranchSlt, w⟩ : Row p TraceKind).finish.word = output.pc := by rfl
  rw [finish]
  have linked {s' : RV.State} (same : RV.Same s' ((before.setReg entry.data.rd output.destination.toBitVec).setPC
      output.pc.toBitVec)) : RV.Same s' { after with pc := output.pc.toBitVec } :=
    same.trans (rv_same_setPC written _)
  -- The instruction is one of the three row kinds.
  obtain ⟨pcE, bitsE, data⟩ := entry
  change rvDecoderFields i = some data at fields
  change RVRowFacts w before data at facts
  change RV.Same after (before.setReg data.rd _) at written
  change ∀ {s' : RV.State}, RV.Same s' ((before.setReg data.rd output.destination.toBitVec).setPC
    output.pc.toBitVec) → RV.Same s' { after with pc := output.pc.toBitVec } at linked
  unfold rvDecoderFields at fields
  split at fields
  -- Comparisons.
  case h_1 rd rs1 rs2 =>
    split_ifs at fields
    obtain rfl := Option.some.inj fields
    obtain ⟨s', exec, same⟩ := rv_comparison_exec hp (output := output)
      (input := ⟨.slt, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, 0, before⟩) facts rfl rfl rfl rfl
    exact ⟨s', exec, linked same⟩
  case h_2 rd rs1 rs2 =>
    split_ifs at fields
    obtain rfl := Option.some.inj fields
    obtain ⟨s', exec, same⟩ := rv_comparison_exec hp (output := output)
      (input := ⟨.sltu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, 0, before⟩) facts rfl rfl rfl rfl
    exact ⟨s', exec, linked same⟩
  case h_3 rd rs1 imm =>
    split_ifs at fields
    obtain rfl := Option.some.inj fields
    simp only [RV.Shape] at shape
    rcases shape with ⟨_, x, rfl⟩ | ⟨kind, _⟩
    · obtain ⟨s', exec, same⟩ := rv_comparison_exec hp (output := output)
        (input := ⟨.slti, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, 0, rd, x, before⟩) facts rfl rfl rfl rfl
      exact ⟨s', exec, linked same⟩
    · simp at kind
  case h_4 rd rs1 imm =>
    split_ifs at fields
    obtain rfl := Option.some.inj fields
    simp only [RV.Shape] at shape
    rcases shape with ⟨_, x, rfl⟩ | ⟨kind, _⟩
    · obtain ⟨s', exec, same⟩ := rv_comparison_exec hp (output := output)
        (input := ⟨.sltiu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, 0, rd, x, before⟩) facts rfl rfl rfl rfl
      exact ⟨s', exec, linked same⟩
    · simp at kind
  -- Branches: the destination is x0.
  case h_5 cond rs1 rs2 offset =>
    obtain rfl := Option.some.inj fields
    simp only [RV.Shape] at shape
    obtain ⟨x, rfl⟩ := shape
    obtain ⟨s', exec, same⟩ := rv_branch_exec hp (output := output)
      (input := ⟨cond, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, x, before⟩) facts
      (decode_branch_even decodes) rfl rfl
    refine ⟨s', exec, same.trans (rv_same_setPC (written.trans (rv_same_set_zero before _)) _)⟩
  -- Jumps.
  case h_6 rd offset =>
    obtain rfl := Option.some.inj fields
    simp only [RV.Shape] at shape
    obtain ⟨x, rfl⟩ := shape
    obtain ⟨s', exec, same⟩ := rv_jump_exec hp (output := output)
      (input := ⟨.jal x, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, 0, rd, before⟩) facts
      (fun offset jal => by cases jal; exact decode_jal_even decodes) rfl rfl rfl rfl
    exact ⟨s', exec, linked same⟩
  case h_7 rd rs1 offset =>
    obtain rfl := Option.some.inj fields
    simp only [RV.Shape] at shape
    obtain ⟨x, rfl⟩ := shape
    obtain ⟨s', exec, same⟩ := rv_jump_exec hp (output := output)
      (input := ⟨.jalr x, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rd, before⟩) facts
      (fun offset jal => by cases jal) rfl rfl rfl rfl
    exact ⟨s', exec, linked same⟩
  case h_8 => cases fields

/-- Every row of an accepted RV-decoded trace preserves x0. -/
theorem rv_zero_preserving {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : NativeTrace p} (accepted : Accepted trace) {initial : RV.State} {addresses : List (BitVec 32)}
    {program : List RVProgramEntry}
    (image : rvProgramImageWith rvDecoderFields initial addresses = some program)
    (decoded : RVDecoded trace program) : ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, present, _, query⟩ := rv_decoder_member (decoded row member)
  obtain ⟨_, _, i, _, fields⟩ := rvProgram_entry_fetch image entry present
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  exact RVZero.jumpBranch_row_zero_preserving hp row core entry fields query
    (rv_decoder_selectors hp core (rv_decoder_field_bounds fields).2.1 query)

/-- Every operand read of an accepted RV-decoded trace seeded by an RV image is a bounded word. -/
theorem rv_value_bounds {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List RVProgramEntry}
    (programImage : rvProgramImageWith rvDecoderFields initial addresses = some program)
    (decoded : RVDecoded trace program) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have sources : WriteSources trace := by
    intro row member
    obtain ⟨entry, present, _, query⟩ := rv_decoder_member (decoded row member)
    obtain ⟨_, _, i, _, fields⟩ := rvProgram_entry_fetch programImage entry present
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
    have pcWord := rv_native_query_pc_word limbSize query
    change Word.mk (row.assignment 0).val (row.assignment 1).val = Word.ofBitVec entry.pc at pcWord
    have initialLo : (row.assignment 0).val < limbBase := by
      have bound := pcWord.symm ▸ Word.ofBitVec_bound entry.pc
      exact bound.1
    exact rv_row_write_sources hp row core fields
      (rv_decoder_selectors limbSize core (rv_decoder_field_bounds fields).2.1 query) initialLo
  exact read_bounds_of_sources (by dsimp [timestampBase]; omega) inverse accepted clocks
    (RVValues.rv_image_bounds image) sources

/-- `JumpBranchSlt.RVTraceSoundnessClaim`, proved. -/
theorem rv_trace_execution {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry}
    (inputs : RVExecutionInputs trace initial cells program)
    (accepted : Accepted trace) (decoded : RVDecoded trace program) :
    RVRealizes trace initial cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, image⟩ := inputs.programImage
  have bounds := rv_value_bounds hp inverse accepted inputs.clocks inputs.image image decoded
  have incoming : ∀ row ∈ trace.rows, row.start.word.Bounded := by
    intro row member
    obtain ⟨entry, _, _, query⟩ := rv_decoder_member (decoded row member)
    have canonical := rv_native_query_pc_word limbSize query
    change row.start.word = Word.ofBitVec entry.pc at canonical
    exact canonical.symm ▸ Word.ofBitVec_bound entry.pc
  have outgoing := outgoing_pc_bounds accepted incoming inputs.terminalCanonical
  refine rv_family_realizes clockSize inverse accepted inputs.toRVNativeInputs
    (rv_zero_preserving limbSize accepted image decoded)
    (rv_family_row_steps limbSize image (fun _ _ => True)
      (fun row member => by
        obtain ⟨entry, present, _, query⟩ := rv_decoder_member (decoded row member)
        exact ⟨entry, present, trivial, query⟩) ?_)
  intro row member entry _ _ query i decodes fields guard before after pc _ history
  obtain ⟨family, w⟩ := row
  cases family
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have read (k : Fin 2) := bounds _ member importedConstraintsMemoryPorts[k]
    (by change importedConstraintsMemoryPorts[k] ∈ importedConstraintsMemoryPorts
        fin_cases k <;> simp [importedConstraintsMemoryPorts])
  have leftBound : (Word.mk (w 22).val (w 23).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using read 0
  have rightBound : (Word.mk (w 26).val (w 27).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using read 1
  have finish := outgoing _ member
  change (Word.mk (w 16).val (w 17).val).Bounded at finish
  exact rv_row_step hp core query decodes fields guard.2 leftBound rightBound finish.2 trace.memoryEpoch pc history

end Airbender.JumpBranchSlt.Proofs

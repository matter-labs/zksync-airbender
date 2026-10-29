import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.UnifiedReduced.PCRelativePreparation
import Airbender.Proofs.UnifiedReduced.ControlPreparation

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem auipc_fields {register : BitVec 5} {immediate : BitVec 20} (nonzero : register ≠ 0) :
    Mixed.decoderFields (.UTYPE (immediate, .Regidx register, .AUIPC)) =
      some ⟨.machine, 0, 0, register, Word.ofBitVec (immediate ++ (0 : BitVec 12)), 4, 0⟩ := by
  change register ≠ 0#5 at nonzero
  simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
    UnifiedReduced.arithmeticFields, Trace.arithmeticFields, DecoderData.mapFamily, nonzero]

theorem auipc_result [Fact p.Prime] (hp : FieldCapacity.NoWrap p 196608)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) (selected : w 13 = 1)
    (pc : (Word.mk (w 0).val (w 1).val).Bounded)
    (immediate : (Word.mk (w 8).val (w 9).val).Bounded) :
    (Word.mk (w 50).val (w 51).val).toBitVec =
      (Word.mk (w 0).val (w 1).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec := by
  have other := UnifiedReduced.Proofs.dispatch_exclusive (by omega) h active 2 selected
  have flags : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0 ∧ w 15 = 0 ∧ w 16 = 0 ∧ w 17 = 0 ∧ w 20 = 0 := by
    repeat' apply And.intro
    all_goals first
      | exact other 0 (by decide) | exact other 1 (by decide)
      | exact other 3 (by decide) | exact other 4 (by decide)
      | exact other 5 (by decide) | exact other 6 (by decide)
      | exact other 9 (by decide)
  have low := Verification.assertion_of_holds h ⟨4, by rw [UnifiedReduced.constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨5, by rw [UnifiedReduced.constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected, flags.1, flags.2.1, flags.2.2.1, flags.2.2.2.1, flags.2.2.2.2.1,
    flags.2.2.2.2.2.1, flags.2.2.2.2.2.2] at low high
  have carry := boolean_val (UnifiedReduced.Proofs.local_flags h 21)
  have overflow := boolean_val (UnifiedReduced.Proofs.local_flags h 20)
  change (w 53).val ≤ 1 at carry
  change (w 52).val ≤ 1 at overflow
  have loEq : ((w 0).val : ZMod p) + 0 + (w 8).val = (w 50).val + 65536 * (w 53).val := by
    simp only [ZMod.natCast_zmod_val]
    linear_combination low
  have hiEq : ((w 53).val : ZMod p) + (w 1).val + 0 + (w 9).val = (w 51).val + 65536 * (w 52).val := by
    simp only [ZMod.natCast_zmod_val]
    linear_combination high
  simpa [Word.toBitVec, Word.value] using Word.add_of_limbs
    (left := ⟨(w 0).val, (w 1).val⟩) (right := ⟨0, 0⟩) (immediate := ⟨(w 8).val, (w 9).val⟩)
    (output := ⟨(w 50).val, (w 51).val⟩) hp pc (by constructor <;> decide) immediate
    (UnifiedReduced.Proofs.destination_bounds h) (Nat.le_trans carry (by decide)) (Nat.le_trans overflow (by decide))
    (by simpa only [Nat.cast_zero] using loEq) (by simpa only [Nat.cast_zero] using hiEq)

theorem pc_relative_preparation_entry [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {register : BitVec 5} {immediate : BitVec 20}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PCRelativePreparation data program cut register immediate)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (last : Delegation.Caller.startClock row + 4 = cut)
    {entry : UnifiedReduced.ProgramEntry} (present : entry ∈ program) (query : row.decoderQuery = entry.query) :
    entry.pc = wrappedProgramAddress data (cut - 4) ∧
      entry.instruction = .UTYPE (immediate, .Regidx register, .AUIPC) := by
  have schedule := wrapped_program_pc_clock hp inverse setup accepted publicProgram ordinaryProgram scope.registry row member
  have pc := native_query_pc_word (by dsimp [limbBase]; omega) query
  have bits : row.start.word.toBitVec = entry.pc := by
    change row.start.word = Word.ofBitVec entry.pc at pc
    rw [pc, Word.ofBitVec_roundtrip]
  have clock : Delegation.Caller.startClock row = cut - 4 := by omega
  have address : entry.pc = wrappedProgramAddress data (cut - 4) := by
    simpa only [bits, clock, wrappedProgramAddress] using schedule
  exact ⟨address, scope.atCut entry present address⟩

theorem auipc_row_output [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {register : BitVec 5} {immediate : BitVec 20}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PCRelativePreparation data program cut register immediate) (nonzero : register ≠ 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address = (Cell.register register).addressCode ∧
      (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).word.toBitVec =
        pcRelativeControl data cut immediate := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  obtain ⟨entry, present, _, query⟩ := decoder_member (accepted.ordinaryDecoded _ member ordinary)
  have shape := pc_relative_preparation_entry hp inverse setup accepted publicProgram ordinaryProgram scope member last present query
  change decoderQuery w = entry.query at query
  have fields := (run_program_sources ordinaryProgram entry present).fields
  rw [shape.2, auipc_fields nonzero] at fields
  have metadata : entry.data = ⟨.machine, 0, 0, register, Word.ofBitVec (immediate ++ (0 : BitVec 12)), 4, 0⟩ :=
    (Option.some.inj fields).symm
  have flags := UnifiedReduced.Proofs.decoder_selectors (by omega) core
    (by rw [metadata]; change 4 < 524288; decide) query
  have selected : w 13 = 1 := by simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 2
  have destinationRAM : w 29 = 0 := by
    simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 18
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  have target : (w 7).val = register.toNat := by simpa [metadata, importedConstraintsDecoderColumns] using indices.2.2
  have lower := Verification.assertion_of_holds core ⟨28, by rw [UnifiedReduced.constraint_count]; decide⟩
  have upper := Verification.assertion_of_holds core ⟨29, by rw [UnifiedReduced.constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, destinationRAM] at lower upper
  have location : w 44 = w 7 := by linear_combination lower
  have top : w 45 = 0 := by linear_combination upper
  have pc := native_query_pc_word (by dsimp [limbBase]; omega) query
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at pc
  have imm := native_query_immediate_word (by dsimp [limbBase]; omega)
    (by rw [metadata]; exact Word.ofBitVec_bound _) query
  change Word.mk (w 8).val (w 9).val = entry.data.immediate at imm
  rw [metadata] at imm
  have result := auipc_result (by omega) core (accepted.active _ member) selected
    (pc.symm ▸ Word.ofBitVec_bound entry.pc) (imm.symm ▸ Word.ofBitVec_bound _)
  rw [pc, imm, Word.ofBitVec_roundtrip, Word.ofBitVec_roundtrip, shape.1] at result
  constructor
  · simp [writeToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, pairCode,
      destinationRAM, location, top, target]
  · simpa [write_word, importedConstraintsMemoryPorts, WordColumns.evaluate, pcRelativeControl] using result

theorem pc_relative_preparation_token [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {immediate : BitVec 20}
    {tokens : List (MemoryToken p)}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (scope : PCRelativePreparation data program cut register immediate) (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧ token.word = Word.ofBitVec (pcRelativeControl data cut immediate) := by
  obtain ⟨w, member, last, ordinary, present, timestamp, bounded⟩ := preparation_output_token hp clockInverse
    accepted publicProgram initialization scope.prefixScope scope.afterInitial scope.beforeTerminal aligned matching
  let token := writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]
  have output := auipc_row_output (by omega) clockInverse setup accepted publicProgram ordinaryProgram scope nonzero member ordinary last
  have word : token.word = Word.ofBitVec (pcRelativeControl data cut immediate) := by
    apply Word.eq_of_value bounded (Word.ofBitVec_bound _)
    have equal := congrArg BitVec.toNat output.2
    rw [Word.toBitVec_toNat bounded] at equal
    exact equal.trans (Word.ofBitVec_value _).symm
  exact ⟨token, present, output.1, timestamp, word⟩

theorem pc_relative_preparation_at_boundary [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before atCut : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {immediate : BitVec 20}
    {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (scope : PCRelativePreparation data program cut register immediate) (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) (boundary : NativeBoundary tokens atCut cells) :
    PCRelativePreparedControl data tokens atCut cut register immediate := by
  obtain ⟨token, present, address, timestamp, word⟩ := pc_relative_preparation_token hp clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.initialization scope nonzero aligned matching
  obtain ⟨cell, _, code, read⟩ := native_boundary_read boundary present
  have same : cell = Cell.register register := cell_address_injective (code.trans address)
  subst cell
  have bits : token.word.toBitVec = pcRelativeControl data cut immediate := by rw [word, Word.ofBitVec_roundtrip]
  exact ⟨bits ▸ read, token, present, address, timestamp, word⟩

theorem pc_relative_control_preparation [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p) (rotationInverse : SerializedInverse.Scale64 p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {immediate : BitVec 20}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (scope : PCRelativePreparation data program cut register immediate) (nonzero : register ≠ 0) (aligned : cut % 4 = 0) :
    PCRelativePreparedBoundaryExecution data before cells cut register immediate := by
  have floor := scope.afterInitial
  have window := mixed_window_execution hp clockInverse rotationInverse accepted inputs aligned aligned (by omega) (by omega)
  obtain ⟨start, finish, earlier, current, atStart, atFinish, earlierPerm, _, earlierHistory, _,
    matching, _, boundary, _⟩ := window.execution
  exact ⟨start, earlier, atStart, earlierPerm, earlierHistory, boundary,
    pc_relative_preparation_at_boundary hp clockInverse accepted inputs scope nonzero aligned matching boundary⟩

end Airbender.UnifiedReduced.Caller.Proofs

module
public import Slop.Trace.RVPooled.Oracle
public import Slop.Trace.RVPooled.Soundness
public import Slop.Trace.RVRealizesInput
public import Human.Trace.RVSoundness

@[expose] public section

/-! The six-family claim with the CSR 0x7C0 forms over our spec (`NonDeterminism.Pooled.RVNativeSoundnessClaim`).
    The input stream is `initial.input`. A read row (ADD/SUB selector 8) writes its response columns to `rd`, and
    `StreamPorts` makes that response the stream's word at the row's clock-ordered read index; so `RV.exec` of the
    read from the input left by the earlier reads gives the row's history. Every other row reads no input
    (`RV.exec_input_irrel`): a write is the NOP row, the rest are the standard rows (`rv_pooled_row_step`). The
    composition carries the input (`rv_realizes_input`). -/

namespace Airbender.Trace.Proofs
open Arithmetic NonDeterminism.Pooled

/-- An ADD/SUB row's read selector is bit 8 of its entry's mask. -/
theorem rv_oracle_isRead {p : Nat} [Fact p.Prime] (hp : limbBase < p) {trace : PooledTrace p}
    {initial : RV.State} {cells : List Cell} {w : Nat → ZMod p} {before after : RV.State}
    {entry : RVPooledProgramEntry}
    (facts : RVPooledRowFacts trace initial cells ⟨.addSub, w⟩ before after entry)
    {d : DecoderData} (data : entry.data = d.mapFamily pooledArithmeticFamily) (small : d.mask < 512) :
    isRead (⟨.addSub, w⟩ : Row p PooledFamily) = d.mask.testBit 8 := by
  have constraints := facts.constraints
  have query := facts.query
  obtain ⟨pc, bits, entryData⟩ := entry
  change entryData = _ at data
  subst data
  have query' : (⟨.addSub, w⟩ : Row p).decoderQuery = (⟨pc, bits, d⟩ : RVProgramEntry).query := query
  have flags := rv_row_query_selectors_of_bound hp trace.rom.wordMemory constraints small query'
  change ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] =
    if d.mask.testBit i.val then 1 else 0 at flags
  have flag := flags ⟨8, by decide⟩
  change w 18 = if d.mask.testBit 8 then 1 else 0 at flag
  change (w 18 == 1) = _
  rw [flag]
  cases d.mask.testBit 8 <;> simp

/-- A row whose instruction reads no input takes the same step from any input. -/
theorem rv_step_lift_input {p : Nat} [Fact p.Prime] {row : Row p PooledFamily} {before after : RV.State}
    {i : RV.Instr} (noRead : i.readsInput = false) (step : RVPooledRowStep row before after i)
    (input : List RV.Word) :
    ∃ next, RV.exec (before.withInput input) i = some next ∧
      RV.Same next (({ after with pc := row.finish.word.toBitVec } : RV.State).withInput input) := by
  obtain ⟨next, exec, same⟩ := step
  refine ⟨next.withInput input, by rw [RV.exec_input_irrel before i noRead input, exec]; rfl, ?_⟩
  exact ⟨same.1, same.2.1, same.2.2.1, same.2.2.2.1, rfl⟩

/-- The standard table has no input read. -/
theorem rv_pooled_no_read {i : RV.Instr} {data : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields i = some data) : i.readsInput = false := by
  cases i <;> first
    | rfl
    | simp [rvPooledDecoderFields, Trace.rvDecoderFields, JumpBranchSlt.rvDecoderFields, MulDiv.rvDecoderFields,
        ShiftBinop.rvDecoderFields, SubwordMemory.rvDecoderFields] at fields

/-- A standard row is not a read row. -/
theorem rv_pooled_not_read {p : Nat} [Fact p.Prime] (hp : limbBase < p) {trace : PooledTrace p}
    {initial : RV.State} {cells : List Cell} {row : Row p PooledFamily} {before after : RV.State}
    {entry : RVPooledProgramEntry} {i : RV.Instr}
    (facts : RVPooledRowFacts trace initial cells row before after entry)
    (fields : rvPooledDecoderFields i = some entry.data) : isRead row = false := by
  obtain ⟨family, w⟩ := row
  cases family
  · obtain ⟨d, fd, data⟩ := (rv_pooled_fields_family fields).1 (Or.inl facts.family)
    have small := (rv_decoder_field_bounds fd).2
    rw [rv_oracle_isRead hp facts data (by omega)]
    exact Nat.testBit_eq_false_of_lt (by omega)
  all_goals rfl

/-- Every row of an accepted trace decoded against an extended program takes one `RV.step` with the input left by
    the earlier reads. -/
theorem rv_oracle_row_steps {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {program : List RVPooledProgramEntry}
    (native : RVNativeInputs NonDeterminism.Pooled.rvDecoderFields trace initial cells program)
    (wordTable : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells))
    (subwordTable : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial))
    (terminalPC : trace.terminal.word.Bounded) (accepted : Accepted trace)
    (decoded : RVPooledDecoded trace program) (ports : StreamPorts trace initial.input) :
    RVRowStepsInput trace initial cells isRead (readIndex trace) := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, programImage⟩ := native.programImage
  have bounds := rv_oracle_value_bounds (by omega) inverse accepted native.clocks native.image wordTable
    subwordTable programImage decoded
  have finishBounds := JumpBranchSlt.Proofs.rv_pooled_finish_bounds limbSize accepted decoded terminalPC
  intro row member before after position history
  obtain ⟨entry, i, decodes, fields, stepAt, facts⟩ := rv_pooled_row_facts limbSize programImage accepted decoded
    bounds finishBounds native.aligned wordTable subwordTable member position history
  have stepped (input : List RV.Word) : RV.step (before.withInput input) = RV.exec (before.withInput input) i :=
    stepAt _ rfl rfl
  rcases rv_oracle_fields_cases fields with ⟨rd, nonzero, rfl, data⟩ | ⟨src, rfl, data⟩ | standard
  · -- A read: `rd` gets the stream's word at the row's read index.
    have tag := rv_oracle_addsub facts.family data rfl
    obtain ⟨kind, w⟩ := row
    change kind = .addSub at tag
    subst tag
    obtain ⟨-, -, written, finish⟩ := rv_addsub_frame hp inverse facts data
    have selected : isRead (⟨.addSub, w⟩ : Row p PooledFamily) = true := by
      rw [rv_oracle_isRead limbSize facts data (show (256 : Nat) < 512 by decide)]
      show Nat.testBit 256 8 = true
      decide
    have value := ports _ member selected
    obtain ⟨bound, word⟩ := List.getElem?_eq_some_iff.mp value
    change readIndex trace ⟨.addSub, w⟩ < initial.input.length at bound
    change initial.input[readIndex trace ⟨.addSub, w⟩] = response ⟨.addSub, w⟩ at word
    have drop : initial.input.drop (readIndex trace ⟨.addSub, w⟩) =
        response ⟨.addSub, w⟩ :: initial.input.drop (readIndex trace ⟨.addSub, w⟩ + 1) := by
      rw [List.drop_eq_getElem_cons bound, word]
    refine ⟨_, (stepped _).trans (by rw [drop]; rfl), ?_⟩
    rw [ite_eq_left selected]
    exact ⟨finish.symm, fun j => (written.2.1 j).symm, written.2.2.1.symm, written.2.2.2.1.symm, rfl⟩
  · -- A write: the NOP row.
    have tag := rv_oracle_addsub facts.family data rfl
    obtain ⟨kind, w⟩ := row
    change kind = .addSub at tag
    subst tag
    have notRead : isRead (⟨.addSub, w⟩ : Row p PooledFamily) = false := by
      rw [rv_oracle_isRead limbSize facts data (show (1 : Nat) < 512 by decide)]
      decide
    obtain ⟨next, exec, same⟩ := rv_step_lift_input rfl
      (rv_nop_row_step hp inverse facts data (i := .inputWrite src) ⟨_, rfl, RV.Same.refl _⟩) (initial.input.drop (readIndex trace _))
    refine ⟨next, (stepped _).trans exec, ?_⟩
    rw [ite_eq_right (by simp [notRead]), Nat.add_zero]
    exact same
  · -- A standard row reads no input.
    obtain ⟨next, exec, same⟩ := rv_step_lift_input (rv_pooled_no_read standard)
      (rv_pooled_row_step hp inverse facts standard decodes) (initial.input.drop (readIndex trace row))
    refine ⟨next, (stepped _).trans exec, ?_⟩
    rw [ite_eq_right (by simp [rv_pooled_not_read limbSize facts standard]), Nat.add_zero]
    exact same

/-- `NonDeterminism.Pooled.RVNativeSoundnessClaim` for any field, given the zero seed of the tracked cells. -/
theorem rv_oracle_trace_execution {p : Nat} [Fact p.Prime] (clockLaws : ClockLaws PooledFamily p)
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p}
    {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    {inits : List (InitsTeardowns.Witness p InitsTeardowns.importedLayout)}
    (inputs : RVPooledBootInputs trace initial cells program inits NonDeterminism.Pooled.rvDecoderFields)
    (seed : trace.initialMemory = ROMView.nativeBootImage cells)
    (accepted : Accepted trace) (decoded : RVPooledDecoded trace program)
    (ports : StreamPorts trace initial.input) :
    NonDeterminism.Pooled.RVRealizes trace initial cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have native := inputs.native (by omega) seed
  obtain ⟨addresses, programImage⟩ := inputs.programImage
  have zero := RVZero.rv_zero_writes_of_preserving clockSize inverse accepted native.clocks inputs.image
    (rv_oracle_zero_preserving (by omega) accepted programImage decoded)
  exact rv_realizes_input clockSize inverse accepted native.clocks inputs.image inputs.distinct inputs.aligned
    zero inputs.start isRead (readIndex trace) (fun _ _ => rfl)
    (rv_oracle_row_steps hp inverse native inputs.wordTable inputs.subwordSetup inputs.terminalPC accepted
      decoded ports)

end Airbender.Trace.Proofs

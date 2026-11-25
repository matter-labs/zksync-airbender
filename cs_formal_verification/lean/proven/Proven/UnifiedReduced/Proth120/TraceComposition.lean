module
public import Proven.UnifiedReduced.Proth120.TraceLaws
public import Proven.UnifiedReduced.Proth120.TraceStream
public import Proven.Trace.RVRealizes
public import Proven.Trace.RVRom

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace Trace.Proofs Arithmetic

private theorem exec_same {s t : RV.State} (h : RV.Same s t) (i : RV.Instr) :
    RV.SameOpt (exec s i) (exec t i) := by
  have hload : s.loadViewAt romEnd = t.loadViewAt romEnd := by
    funext a
    simp only [RV.State.loadViewAt, h.2.2.1, h.2.2.2.1]
  have ordinary := RV.exec_same h i
  cases i <;> try exact ordinary
  case load n signed rd rs1 off =>
    simp only [exec, RV.execAt, h.2.1, hload]
    split
    · exact h.nextInstr
    · split
      · exact (h.setReg rd _).nextInstr
      · trivial
  case store n rs2 rs1 off =>
    simp only [exec, RV.execAt, h.2.1]
    split
    · exact (h.store _ _ _).nextInstr
    · trivial

private theorem step_same {s t : RV.State} (h : RV.Same s t) : RV.SameOpt (step s) (step t) := by
  unfold step RV.stepAt
  rw [h.1, h.2.2.1]
  split
  · cases RV.decode (RV.read t.rom t.pc 4) with
    | none => trivial
    | some i => exact exec_same h i
  · trivial

/-- Compose the accepted rows backwards along the derived state chain and native memory history.
    The induction advances the wrap interpreter by exactly one instruction per row. -/
private theorem compose (rowSound : RowSoundnessClaim) (csrSound : CSRRowSoundnessClaim) {trace : WrapTrace} {initial cells}
    (inputs : TraceInputs trace initial cells) (accepted : Accepted trace) :
    ∀ (rows : List (Row proth120Modulus Kind)) (terminal : PCState.State proth120Modulus) {after : RV.State},
      (∀ row ∈ rows, row ∈ trace.rows) →
      rows.Pairwise (fun a b => b.clock < a.clock) →
      (∀ r ∈ rows, ExternalStream.index Row.clock isRead trace.rows r = ExternalStream.index Row.clock isRead rows r) →
      ((terminal, terminal) :: rows.map (fun r => (r.start, r.finish)) ++ [(trace.initial, trace.initial)]).IsChain
        (fun a b => a.1 = b.2) →
      RVHistory cells (rows.flatMap fun r => (rowEvents trace.memoryEpoch r).reverse) initial after →
      ∃ final, run rows.length initial = some final ∧ RV.Same final {after with pc := terminal.word.toBitVec, input := initial.input.drop (ExternalStream.count isRead rows)}
  | [], terminal, after, _, _, _, chain, history => by
    have endEq : terminal = trace.initial := by simpa using chain
    cases history
    exact ⟨initial, rfl, ⟨endEq ▸ inputs.pc, fun _ => rfl, rfl, rfl, rfl⟩⟩
  | row :: rest, terminal, after, members, sorted, positions, chain, history => by
    obtain ⟨middle, past, current⟩ := rv_history_append.mp history
    have linked : terminal = row.finish ∧
        ((row.start, row.start) :: rest.map (fun r => (r.start, r.finish)) ++ [(trace.initial, trace.initial)]).IsChain
        (fun a b => a.1 = b.2) := by
      cases rest <;> simpa only [List.map_cons, List.map_nil, List.nil_append, List.cons_append,
        List.isChain_cons_cons] using chain
    rcases linked with ⟨rfl, linked⟩
    obtain ⟨final, ran, same⟩ := compose rowSound csrSound inputs accepted rest row.start
      (fun r hr => members r (List.mem_cons_of_mem _ hr)) (List.pairwise_cons.mp sorted).2
      (fun r hr => (positions r (List.mem_cons_of_mem _ hr)).trans (tail_position sorted hr)) linked past
    have member := members row List.mem_cons_self
    let k := ExternalStream.count isRead rest
    let before := {middle with pc := row.start.word.toBitVec, input := initial.input.drop k}
    let after' := {after with pc := row.start.word.toBitVec, input := initial.input.drop k}
    have atIndex : ExternalStream.index Row.clock isRead trace.rows row = k :=
      (positions row List.mem_cons_self).trans (read_position sorted)
    have rom : middle.rom = initial.rom := rvWriteHistory_rom past.writes
    obtain ⟨alignedPC, inROM, decoded⟩ := inputs.decoded row member
    have context : RowContext cells trace.memoryEpoch row.assignment before after' := {
      active := accepted.active row member
      fetch := ⟨alignedPC, inROM⟩
      bounded := read_bounds inputs accepted row member
      aligned := inputs.aligned
      history := by
        simpa [rowEvents, nativeRowEvents, MemoryPort.event, Row.columns, Row.ports, CircuitLayout.columns,
          CircuitLayout.ports, before, after'] using
            history_with_input (rv_history_with_pc current row.start.word.toBitVec) (initial.input.drop k) }
    have core := Verification.holds_of_sublist (accepted.constraints row member)
      (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
    rw [inputs.setup, ← show ROM.wordsRV before = ROM.wordsRV initial by funext j; simp only [ROM.wordsRV, before, rom]] at core
    have result : StepResult row.assignment before {after' with input := before.input.drop (isRead row).toNat} := by
      rcases decoded with ⟨noRead, dec⟩ | csr
      · have inp : RowInputs cells trace.memoryEpoch row.assignment before after' := ⟨context, core, by
          simpa [Decoded, before, rom, Row.columns, Row.decoderColumns, CircuitLayout.columns,
            CircuitLayout.decoderColumns] using dec⟩
        simpa [noRead, before, after'] using rowSound _ _ _ _ _ inp
      · apply csrSound cells trace.memoryEpoch _ _ _ _ ⟨context, core, ?_, ?_⟩
        · simpa [CSRDecoded, before, rom, Row.columns, Row.decoderColumns, CircuitLayout.columns,
            CircuitLayout.decoderColumns] using csr
        · intro selected
          simpa [before, List.head?_drop, atIndex] using inputs.stream row member selected
    obtain ⟨next, stepped, agree⟩ := result
    obtain ⟨actual, actualStep, agree'⟩ := (step_same same.symm).some_left stepped
    refine ⟨actual, ?_, ?_⟩
    · change (run rest.length initial).bind step = some actual
      rw [ran]
      exact actualStep
    have len : ExternalStream.count isRead (row :: rest) = k + (isRead row).toNat := by
      cases h : isRead row <;> simp [ExternalStream.count, k, h]
    simpa only [len, before, after', List.drop_drop, Nat.add_comm (isRead row).toNat k,
      Row.finish, PCState.State.word, rawPair, Row.columns, CircuitLayout.columns] using agree'.symm.trans agree

/-- The unordered matching and strict port clocks recover the chronological row order and the
    complete tracked-cell history. The local x0 preservation law supplies the architecture's fixed register. -/
theorem trace_of_rows (rowSound : RowSoundnessClaim) (csrSound : CSRRowSoundnessClaim) {trace : WrapTrace} {initial cells}
    (inputs : TraceInputs trace initial cells) (accepted : Accepted trace)
    (zero : ∀ e ∈ trace.nativeEvents, e.2.1 = (Cell.register 0).addressCode → memoryWord e.2.2.2 = 0) :
    TraceResult trace initial cells := by
  have large : 2 * timestampBase + 4 < proth120Modulus := by decide
  obtain ⟨hist, rows, after, consistent, permutation, ordered, events, matched⟩ :=
    rv_native_row_history large time_inverse accepted inputs.clocks inputs.image inputs.distinct inputs.aligned zero
  have chain := ordered_row_boundaries large time_inverse accepted inputs.clocks permutation ordered
  obtain ⟨final, ran, same⟩ := compose rowSound csrSound inputs accepted rows trace.terminal
    (fun _ h => permutation.mem_iff.mp h) ordered (fun r _ => (permutation.filter _).length_eq.symm) chain events
  refine ⟨final, permutation.length_eq ▸ ran, (by simpa [ExternalStream.count, (permutation.filter isRead).length_eq] using same.2.2.2.2), same.1, ?_⟩
  intro sink member
  obtain ⟨c, present, code, read⟩ := rv_terminal_reads large time_inverse accepted inputs.clocks inputs.image
    inputs.distinct consistent matched sink member
  refine ⟨c, present, code, ?_⟩
  rw [readRV_congr_same same]
  cases c <;> exact read

end Airbender.UnifiedReduced.Proth120

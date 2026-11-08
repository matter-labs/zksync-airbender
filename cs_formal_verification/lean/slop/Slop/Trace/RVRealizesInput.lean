module
public import Slop.Trace.RVRealizes
public import Slop.ISA.RV.Input

@[expose] public section

/-! Composition on the RV route with the input stream (CSR 0x7C0 reads), for any circuit registry `Kind`: as
    `rv_compose_rows` / `rv_realizes` (`RVRealizes.lean`), but each row starts from the input left after the reads of
    the rows before it (`index`, counted by native clock) and consumes one more word if it is a read (`read`). The
    row positions and histories never move the input (`RVRowPosition`), so the input is carried separately. -/

namespace Airbender.Trace.Proofs
open Arithmetic

variable {Kind : Type} [CircuitLayout Kind]

/-- The per-row obligation with the input: from the row's pre-state with the input after `index row` reads, one
    `RV.step` reaches the row's history followed by its final PC, with `read row` more words consumed. -/
def RVRowStepsInput {p : Nat} [Fact p.Prime] (trace : Data p Kind) (initial : RV.State) (cells : List Cell)
    (read : Row p Kind → Bool) (index : Row p Kind → Nat) : Prop :=
  ∀ row ∈ trace.rows, ∀ {before after : RV.State}, RVRowPosition trace initial cells row before →
    RVHistory cells (rowEvents trace.memoryEpoch row).reverse before after →
    ∃ next, RV.step (before.withInput (initial.input.drop (index row))) = some next ∧
      RV.Same next (({ after with pc := row.finish.word.toBitVec } : RV.State).withInput
        (initial.input.drop (index row + if read row then 1 else 0)))

private theorem input_head_index {p : Nat} (read : Row p Kind → Bool) (index : Row p Kind → Nat)
    {row : Row p Kind} {rows : List (Row p Kind)}
    (ordered : (row :: rows).Pairwise (fun a b => b.clock < a.clock))
    (equal : index row = ((row :: rows).filter fun earlier =>
      read earlier && decide (earlier.clock < row.clock)).length) :
    index row = (rows.filter read).length := by
  rw [equal]
  simp only [List.filter_cons, lt_self_iff_false, decide_false, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply List.filter_congr
  intro old member
  simp [(List.pairwise_cons.mp ordered).1 old member]

private theorem input_remaining_indices {p : Nat} (read : Row p Kind → Bool) (index : Row p Kind → Nat)
    {row : Row p Kind} {rows : List (Row p Kind)}
    (ordered : (row :: rows).Pairwise (fun a b => b.clock < a.clock))
    (indices : ∀ current ∈ row :: rows, index current =
      ((row :: rows).filter fun earlier => read earlier &&
        decide (earlier.clock < current.clock)).length) :
    ∀ current ∈ rows, index current =
      (rows.filter fun earlier => read earlier && decide (earlier.clock < current.clock)).length := by
  intro current member
  have previous := (List.pairwise_cons.mp ordered).1 current member
  have equal := indices current (List.mem_cons_of_mem row member)
  simpa [List.filter_cons, Nat.not_lt.mpr (Nat.le_of_lt previous)] using equal

theorem rv_compose_rows_input {p : Nat} [Fact p.Prime] {trace : Data p Kind} {initial : RV.State}
    {cells : List Cell} (read : Row p Kind → Bool) (index : Row p Kind → Nat)
    (start : initial.pc = trace.initial.word.toBitVec) (step : RVRowStepsInput trace initial cells read index) :
    ∀ (rows newer : List (Row p Kind)) (terminal : PCState.State p) {after : RV.State},
      (newer ++ rows).Perm trace.rows →
      (newer ++ rows).Pairwise (fun a b => b.clock < a.clock) →
      (∀ current ∈ rows, index current =
        (rows.filter fun earlier => read earlier && decide (earlier.clock < current.clock)).length) →
      ((terminal, terminal) :: rows.map (fun row => (row.start, row.finish)) ++
        [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2) →
      RVHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial after →
      ∃ n final, RV.run n initial = some final ∧
        RV.Same final (({ after with pc := terminal.word.toBitVec } : RV.State).withInput
          (initial.input.drop (rows.filter read).length))
  | [], newer, terminal, after, _, _, _, chain, history => by
    have same : terminal = trace.initial := by simpa using chain
    cases history
    exact ⟨0, initial, rfl, ⟨by rw [same, start]; rfl, fun _ => rfl, rfl, rfl, by simp [RV.State.withInput]⟩⟩
  | row :: rest, newer, terminal, after, permutation, ordered, indices, chain, history => by
    have split : RVHistory cells
        ((rowEvents trace.memoryEpoch row).reverse ++
          rest.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse)) initial after := history
    obtain ⟨middle, past, current⟩ := rv_history_append.mp split
    have linked : terminal = row.finish ∧
        ((row.start, row.start) :: rest.map (fun row => (row.start, row.finish)) ++
          [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2) := by
      cases rest <;> simpa only [List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, List.isChain_cons_cons] using chain
    rcases linked with ⟨rfl, linked⟩
    have rearranged : (newer ++ [row]) ++ rest = newer ++ row :: rest := by simp
    have tail : (row :: rest).Pairwise (fun a b => b.clock < a.clock) :=
      ordered.sublist (List.sublist_append_right _ _)
    have headIndex := input_head_index read index tail (indices row List.mem_cons_self)
    obtain ⟨n, final, run, same⟩ := rv_compose_rows_input read index start step rest (newer ++ [row]) row.start
      (rearranged.symm ▸ permutation) (rearranged.symm ▸ ordered)
      (input_remaining_indices read index tail indices) linked past
    have position : RVRowPosition trace initial cells row { middle with pc := row.start.word.toBitVec } := by
      refine ⟨newer, rest, middle, permutation, ordered, ?_, rfl⟩
      simpa only [List.map_flatMap, row_write_values] using RVHistory.writes past
    have member : row ∈ trace.rows := permutation.mem_iff.mp (by simp)
    obtain ⟨next, stepped, agree⟩ := step row member position
      (rv_history_with_pc current row.start.word.toBitVec)
    rw [headIndex] at stepped agree
    obtain ⟨final', finalStep, finalSame⟩ := (RV.step_same same.symm).some_left stepped
    have count : ((row :: rest).filter read).length = (rest.filter read).length + if read row then 1 else 0 := by
      cases selected : read row <;> simp [selected]
    refine ⟨n + 1, final', ?_, ?_⟩
    · rw [RV.run_add, run]
      simp [RV.run, finalStep]
    · rw [count]
      exact finalSame.symm.trans agree

/-- The whole RV composition with the input: an accepted trace whose initial memory is the public RV image, whose
    native writes keep x0 zero, and whose rows each take one `RV.step` with the input left by the earlier reads, is a
    run of our spec that consumes exactly its reads. -/
theorem rv_realizes_input {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory) (domain : cells.Nodup)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0)
    (start : initial.pc = trace.initial.word.toBitVec) (read : Row p Kind → Bool) (index : Row p Kind → Nat)
    (indices : ∀ row ∈ trace.rows, index row =
      (trace.rows.filter fun earlier => read earlier && decide (earlier.clock < row.clock)).length)
    (step : RVRowStepsInput trace initial cells read index) :
    ∃ n after, RV.run n initial = some after ∧ after.input = initial.input.drop (trace.rows.filter read).length ∧
      after.pc = trace.terminal.word.toBitVec ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.readRV after = some sink.word.toBitVec := by
  obtain ⟨history, rows, after, consistent, permutation, ordered, native, matched⟩ :=
    rv_native_row_history hp inverse accepted boundary image domain aligned zero
  have chain := ordered_row_boundaries hp inverse accepted boundary permutation ordered
  have rowIndices : ∀ current ∈ rows, index current =
      (rows.filter fun earlier => read earlier && decide (earlier.clock < current.clock)).length :=
    fun current present => (indices current (permutation.mem_iff.mp present)).trans
      (permutation.filter _).length_eq.symm
  obtain ⟨n, final, run, same⟩ := rv_compose_rows_input read index start step rows [] trace.terminal
    (by simpa using permutation) (by simpa using ordered) rowIndices chain native
  refine ⟨n, final, run, ?_, same.1, ?_⟩
  · rw [same.2.2.2.2, ← (permutation.filter read).length_eq]
    rfl
  · intro sink member
    obtain ⟨cell, present, address, value⟩ := rv_terminal_reads hp inverse accepted boundary image domain
      consistent matched sink member
    refine ⟨cell, present, address, ?_⟩
    rw [readRV_congr_same same]
    cases cell <;> exact value

end Airbender.Trace.Proofs

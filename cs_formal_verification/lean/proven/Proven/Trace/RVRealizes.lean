module
public import Human.Trace.RVExecution
public import Proven.Trace.RVHistory
public import Proven.Trace.RVPooledRow
public import Proven.Trace.CompositionCore
public import Proven.Trace.Terminal
public import Proven.ISA.RV.Step
public import Proven.ISA.RV.Same
public import Proven.Defs.Helpers.Context.Model
public import Proven.Defs.Helpers.Memory.RowEvents
public import Proven.Defs.Helpers.Memory.History

@[expose] public section

/-! Composition on the RV route, for any circuit registry `Kind`: the accepted rows, in their history-derived order,
    compose into `RV.run` from the public starting state (`RVRealizes`). The per-row obligation is one `RV.step` of the
    row's pre-state (`RVRowPosition`) to a state that agrees (`RV.Same`) with the row's RV history followed by its final
    PC. RV sibling of `compose_native_rows_at` / `native_trace_postconditions` (`PositionComposition.lean`,
    `CompositionCore.lean`). -/

namespace Airbender.Trace.Proofs
open Arithmetic

variable {Kind : Type} [CircuitLayout Kind]

/-- The per-row obligation of the composition. -/
def RVRowSteps {p : Nat} [Fact p.Prime] (trace : Data p Kind) (initial : RV.State) (cells : List Cell) : Prop :=
  ∀ row ∈ trace.rows, ∀ {before after : RV.State}, RVRowPosition trace initial cells row before →
    RVHistory cells (rowEvents trace.memoryEpoch row).reverse before after →
    ∃ next, RV.step before = some next ∧ RV.Same next { after with pc := row.finish.word.toBitVec }

private theorem with_pc_same (s : RV.State) (pc : BitVec 32) (h : s.pc = pc) :
    RV.Same s { s with pc := pc } := ⟨h, fun _ => rfl, rfl, rfl, rfl⟩

theorem rv_compose_rows {p : Nat} [Fact p.Prime] {trace : Data p Kind} {initial : RV.State} {cells : List Cell}
    (start : initial.pc = trace.initial.word.toBitVec) (step : RVRowSteps trace initial cells) :
    ∀ (rows newer : List (Row p Kind)) (terminal : PCState.State p) {after : RV.State},
      (newer ++ rows).Perm trace.rows →
      (newer ++ rows).Pairwise (fun a b => b.clock < a.clock) →
      ((terminal, terminal) :: rows.map (fun row => (row.start, row.finish)) ++
        [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2) →
      RVHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial after →
      ∃ n final, RV.run n initial = some final ∧ RV.Same final { after with pc := terminal.word.toBitVec }
  | [], newer, terminal, after, _, _, chain, history => by
    have same : terminal = trace.initial := by simpa using chain
    cases history
    exact ⟨0, initial, rfl, with_pc_same initial _ (by rw [same, start])⟩
  | row :: rest, newer, terminal, after, permutation, ordered, chain, history => by
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
    obtain ⟨n, final, run, same⟩ := rv_compose_rows start step rest (newer ++ [row]) row.start
      (rearranged.symm ▸ permutation) (rearranged.symm ▸ ordered) linked past
    have position : RVRowPosition trace initial cells row { middle with pc := row.start.word.toBitVec } := by
      refine ⟨newer, rest, middle, permutation, ordered, ?_, rfl⟩
      simpa only [List.map_flatMap, row_write_values] using RVHistory.writes past
    have member : row ∈ trace.rows := permutation.mem_iff.mp (by simp)
    obtain ⟨next, stepped, agree⟩ := step row member position
      (rv_history_with_pc current row.start.word.toBitVec)
    obtain ⟨final', finalStep, finalSame⟩ := (RV.step_same same.symm).some_left stepped
    refine ⟨n + 1, final', ?_, finalSame.symm.trans agree⟩
    rw [RV.run_add, run]
    simp [RV.run, finalStep]

/-- RV sibling of `image_sources`: every seed token of the RV image is a public cell's starting value. -/
theorem rv_image_sources {p : Nat} {initial : RV.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImageRV initial cells = some tokens) :
    ∀ token ∈ tokens, ∃ cell ∈ cells, ∃ value, cell.readRV initial = some value ∧ token = cell.initialToken value := by
  have reads := rvImage_reads cells tokens image
  clear image
  induction reads with
  | nil => simp
  | @cons cell token cells tokens head tail ih =>
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨value, read, same⟩ := head
      exact ⟨cell, List.mem_cons_self, value, read, same⟩
    · obtain ⟨source, sourceMember, value, read, same⟩ := ih actual member
      exact ⟨source, List.mem_cons_of_mem _ sourceMember, value, read, same⟩

/-- RV sibling of `terminal_sail_reads`: a state matching the complete history reads the terminal values. -/
theorem rv_terminal_reads {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial after : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory) (domain : cells.Nodup)
    {history : TimestampSortedMemoryAccessList} (consistent : MemoryHistory trace history)
    (realized : RVStateMatches cells history after) :
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.readRV after = some (memoryWord sink.value) := by
  intro sink member
  have keys := boundary_keys MemoryToken.address (memory_steps_matched accepted) memory_steps_address
  obtain ⟨source, present, address⟩ := List.mem_map.mp
    (keys.mem_iff.mpr (List.mem_map.mpr ⟨sink, member, rfl⟩))
  obtain ⟨cell, cellMember, _, _, same⟩ := rv_image_sources image source present
  have code : source.address = cell.addressCode := congrArg MemoryToken.address same
  refine ⟨cell, cellMember, code.symm.trans address, ?_⟩
  have read := realized cell cellMember
  have latest := terminal_latest_value hp inverse accepted boundary
    (rvImage_unique image domain) consistent member
  rw [code.symm.trans address, latest] at read
  exact read

/-- The whole RV composition: an accepted trace whose initial memory is the public RV image, whose native writes
    keep x0 zero, and whose rows each take one `RV.step`, realizes `RV.run`. -/
theorem rv_realizes {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory) (domain : cells.Nodup)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0)
    (start : initial.pc = trace.initial.word.toBitVec) (step : RVRowSteps trace initial cells) :
    RVRealizes trace initial cells := by
  obtain ⟨history, rows, after, consistent, permutation, ordered, native, matched⟩ :=
    rv_native_row_history hp inverse accepted boundary image domain aligned zero
  have chain := ordered_row_boundaries hp inverse accepted boundary permutation ordered
  obtain ⟨n, final, run, same⟩ := rv_compose_rows start step rows [] trace.terminal
    (by simpa using permutation) (by simpa using ordered) chain native
  refine ⟨n, final, run, same.1, ?_⟩
  intro sink member
  obtain ⟨cell, present, address, read⟩ := rv_terminal_reads hp inverse accepted boundary image domain
    consistent matched sink member
  refine ⟨cell, present, address, ?_⟩
  rw [readRV_congr_same same]
  cases cell <;> exact read

end Airbender.Trace.Proofs

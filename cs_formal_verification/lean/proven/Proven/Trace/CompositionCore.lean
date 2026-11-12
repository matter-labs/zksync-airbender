module
public import Proven.Trace.RowHistory
public import Proven.Trace.Terminal
public import Mathlib.Data.List.Chain
public import Mathlib.Logic.Relation
public import Proven.Defs.Helpers.Context.Model

@[expose] public section

namespace Airbender.Trace.Proofs

private theorem path_edge_chain {α : Type} {path : List α} {first last : α}
    (head : path.head? = some first) (endPoint : path.getLast? = some last) :
    ((first, first) :: path.zip path.tail ++ [(last, last)]).IsChain
      (fun a b => a.2 = b.1) := by
  induction path generalizing first with
  | nil => simp at head
  | cons a rest ih =>
    have same : a = first := by simpa using head
    subst first
    cases rest with
    | nil =>
      have same : a = last := by simpa using endPoint
      subst last
      simp
    | cons b rest =>
      have tail := ih (first := b) rfl (by simpa using endPoint)
      cases rest with
      | nil => simpa using tail
      | cons c rest =>
        simp only [List.tail_cons, List.zip_cons_cons, List.cons_append,
          List.isChain_cons_cons] at tail ⊢
        exact ⟨trivial, tail⟩

/-- The sorted native rows connect both public endpoints and every adjacent
    instruction boundary. This is derived from the complete state path. -/
theorem ordered_row_boundaries {Kind : Type} [CircuitLayout Kind] [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {rows : List (Row p Kind)} (permutation : rows.Perm trace.rows)
    (ordered : rows.Pairwise (fun a b => rowClock b < rowClock a)) :
    ((trace.terminal, trace.terminal) ::
      rows.map (fun row => (row.start, row.finish)) ++ [(trace.initial, trace.initial)]).IsChain
      (fun a b => a.1 = b.2) := by
  obtain ⟨path, statePath, edges⟩ :=
    ordered_row_state_path hp inverse accepted boundary permutation ordered
  have chain := path_edge_chain statePath.1 statePath.2.1
  have reversed := List.isChain_reverse.mpr chain
  simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
    List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append, edges] using
    reversed.imp (by intro a b equal; exact equal.symm)

end Airbender.Trace.Proofs

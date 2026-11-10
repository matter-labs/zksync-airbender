module
public import Human.Helpers.Context.RVRowModel

@[expose] public section

/-! One-row witnesses for the `RVRowSatisfiable` conjuncts of the per-row RV claims (lean-strategies 3.3): in a
    trace whose only row is `row`, the row's pre-state is the starting state at the row's PC, and a one-entry program
    whose query is the row's decoder query decodes the trace. -/

namespace Airbender.Trace.Proofs

/-- The only row of a trace starts from the starting state, at its own PC (no earlier writes). -/
theorem rv_row_position_single {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    {trace : Data p Kind} {row : Row p Kind} (rows : trace.rows = [row]) (initial : RV.State) (cells : List Cell) :
    RVRowPosition trace initial cells row { initial with pc := row.start.word.toBitVec } :=
  ⟨[], [], initial, by rw [rows]; exact List.Perm.refl _, List.pairwise_singleton _ _, .nil initial, rfl⟩

/-- A one-row trace is decoded by a one-entry program of the row's family whose query is the row's. -/
theorem rv_pooled_decoded_single {p : Nat} [Fact p.Prime] {trace : PooledTrace p}
    {row : Row p PooledFamily} {entry : RVPooledProgramEntry} (rows : trace.rows = [row])
    (family : entry.data.family = row.family) (query : row.decoderQuery = entry.query) :
    RVPooledDecoded trace [entry] := by
  intro actual member
  rw [rows, List.mem_singleton] at member
  subst member
  exact (rvDecoderTable [entry] actual.family).implied_by_completeness #[] _
    ⟨entry, List.mem_singleton_self _, family, query⟩

end Airbender.Trace.Proofs

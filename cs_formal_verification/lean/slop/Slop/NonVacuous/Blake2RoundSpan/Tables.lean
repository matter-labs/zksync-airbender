module
public import Slop.Blake2Round.Lookups

@[expose] public section

/-! Membership of honest rows in the exported round setup table (the converse of `Slop/Blake2Round/Lookups.lean`):
    a query whose six entries evaluate to `a b c d e t` with the row meaning `RowFacts t a b c d e` of one of the
    six tags is the formula row at that region's index (`SetupProofs.setupRow_eq`). -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Blake2Round.SetupProofs Blake2Round.Proofs

/-- Every row meaning is a formula row. -/
theorem row_of_facts {t a b c d e : Nat} (facts : RowFacts t a b c d e) :
    ∃ i < 1048576, formulaRow i = #v[a, b, c, d, e, t] := by
  unfold RowFacts at facts
  split at facts
  · obtain ⟨ha, hb, rfl, rfl, rfl⟩ := facts
    refine ⟨a * 256 + b, by omega, ?_⟩
    have q : (a * 256 + b) / 256 = a := by omega
    have r : (a * 256 + b) % 256 = b := by omega
    simp only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, q, r, show a * 256 + b < 65536 by omega,
      ↓reduceIte, show a * 256 + b < 344064 by omega, show a * 256 + b < 589824 by omega]
  · obtain ⟨ha, hb, rfl, rfl, rfl⟩ := facts
    refine ⟨65536 + (a * 128 + b), by omega, ?_⟩
    have q : (65536 + (a * 128 + b) - 65536) / 128 = a := by omega
    have r : (65536 + (a * 128 + b) - 65536) % 128 = b := by omega
    simp only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, q, r,
      show ¬ 65536 + (a * 128 + b) < 65536 by omega, show 65536 + (a * 128 + b) < 81920 by omega, ↓reduceIte,
      show 65536 + (a * 128 + b) < 344064 by omega, show 65536 + (a * 128 + b) < 589824 by omega]
  · obtain ⟨ha, hb, rfl, rfl, rfl⟩ := facts
    refine ⟨81920 + (a * 512 + b), by omega, ?_⟩
    have q : (81920 + (a * 512 + b) - 81920) / 512 = a := by omega
    have r : (81920 + (a * 512 + b) - 81920) % 512 = b := by omega
    simp only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, q, r,
      show ¬ 81920 + (a * 512 + b) < 65536 by omega, show ¬ 81920 + (a * 512 + b) < 81920 by omega,
      show 81920 + (a * 512 + b) < 344064 by omega, ↓reduceIte, show 81920 + (a * 512 + b) < 589824 by omega]
  · obtain ⟨ha, hb, hc, rfl, rfl⟩ := facts
    refine ⟨344064 + (c * 65536 + a * 256 + b), by omega, ?_⟩
    have q : (344064 + (c * 65536 + a * 256 + b) - 344064) % 65536 / 256 = a := by omega
    have r : (344064 + (c * 65536 + a * 256 + b) - 344064) % 256 = b := by omega
    have s : (344064 + (c * 65536 + a * 256 + b) - 344064) / 65536 = c := by omega
    simp only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, q, r, s,
      show ¬ 344064 + (c * 65536 + a * 256 + b) < 65536 by omega,
      show ¬ 344064 + (c * 65536 + a * 256 + b) < 81920 by omega,
      show ¬ 344064 + (c * 65536 + a * 256 + b) < 344064 by omega,
      show 344064 + (c * 65536 + a * 256 + b) < 540672 by omega, ↓reduceIte,
      show 344064 + (c * 65536 + a * 256 + b) < 589824 by omega]
  · obtain ⟨ha, hb, hc, rfl, rfl⟩ := facts
    refine ⟨540672 + (c * 16384 + a * 128 + b), by omega, ?_⟩
    have q : (540672 + (c * 16384 + a * 128 + b) - 540672) % 16384 / 128 = a := by omega
    have r : (540672 + (c * 16384 + a * 128 + b) - 540672) % 128 = b := by omega
    have s : (540672 + (c * 16384 + a * 128 + b) - 540672) / 16384 = c := by omega
    simp only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, q, r, s,
      show ¬ 540672 + (c * 16384 + a * 128 + b) < 65536 by omega,
      show ¬ 540672 + (c * 16384 + a * 128 + b) < 81920 by omega,
      show ¬ 540672 + (c * 16384 + a * 128 + b) < 344064 by omega,
      show ¬ 540672 + (c * 16384 + a * 128 + b) < 540672 by omega,
      show 540672 + (c * 16384 + a * 128 + b) < 589824 by omega, ↓reduceIte]
  · obtain ⟨ha, hb, hc, hd, rfl⟩ := facts
    refine ⟨589824 + (a * 1024 + b * 128 + c * 8 + d), by omega, ?_⟩
    have q0 : (589824 + (a * 1024 + b * 128 + c * 8 + d) - 589824) / 1024 = a := by omega
    have q1 : (589824 + (a * 1024 + b * 128 + c * 8 + d) - 589824) / 128 % 8 = b := by omega
    have q2 : (589824 + (a * 1024 + b * 128 + c * 8 + d) - 589824) / 8 % 16 = c := by omega
    have q3 : (589824 + (a * 1024 + b * 128 + c * 8 + d) - 589824) % 8 = d := by omega
    simp only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, q0, q1, q2, q3,
      show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 65536 by omega,
      show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 81920 by omega,
      show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 344064 by omega,
      show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 540672 by omega,
      show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 589824 by omega,
      show 589824 + (a * 1024 + b * 128 + c * 8 + d) < 606208 by omega, ↓reduceIte]
  · exact facts.elim

variable {p : Nat} [Fact p.Prime]

/-- A setup query whose entries evaluate to values with a tag's row meaning is in the table. -/
theorem setup_contains {entry : Vector (Expression (ZMod p)) 6} {env : Environment (ZMod p)} {t : Nat}
    {a b c d e : ZMod p} (facts : RowFacts t a.val b.val c.val d.val e.val)
    (v0 : entry[0].eval env = a) (v1 : entry[1].eval env = b) (v2 : entry[2].eval env = c)
    (v3 : entry[3].eval env = d) (v4 : entry[4].eval env = e) (v5 : entry[5].eval env = (t : ZMod p)) :
    (Lookup.mk Blake2Round.setupTable.toRaw entry).Contains env := by
  obtain ⟨i, bound, row⟩ := row_of_facts facts
  refine ⟨⟨i, lt_of_lt_of_eq bound traceLen_eq.symm⟩, ?_⟩
  change entry.map (Expression.eval env) = (Blake2Round.setupRow i).map (fun (v : Int) => (v : ZMod p))
  rw [setupRow_eq i bound, row]
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_map]
  interval_cases j <;> simp [v0, v1, v2, v3, v4, v5]

end Airbender.NonVacuous.Blake2RoundSpan

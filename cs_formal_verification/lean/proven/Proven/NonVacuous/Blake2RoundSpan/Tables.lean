module
public import Proven.Blake2Round.Lookups

@[expose] public section

/-! Membership of honest rows in the exported round setup table (the converse of `Proven/Blake2Round/Lookups.lean`):
    a query whose six entries evaluate to `a b c d e t` with the row meaning `RowFacts t a b c d e` of one of the
    six tags is the formula row at that region's index (`SetupProofs.setupRow_eq`). -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Blake2Round.SetupProofs Blake2Round.Proofs

/-- A row of tag 4 has its formula index. -/
private theorem row_of_tag4 {a b c d e : Nat} (facts : RowFacts 4 a b c d e) :
  ∃ i < 1048576, formulaRow i = #v[a, b, c, d, e, 4] := by
  simp only [RowFacts] at facts
  obtain ⟨ha, hb, rfl, rfl, rfl⟩ := facts
  refine ⟨a * 256 + b, by as_aux_lemma => omega, ?_⟩
  have q : (a * 256 + b) / 256 = a := by as_aux_lemma => omega
  have r : (a * 256 + b) % 256 = b := by as_aux_lemma => omega
  apply Vector.ext
  intro j hj
  interval_cases j
  · change spec0 (a * 256 + b) = a
    as_aux_lemma =>
      simp only [spec0,
        q,
        show a * 256 + b < 65536 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec1 (a * 256 + b) = b
    as_aux_lemma =>
      simp only [spec1,
        r,
        show a * 256 + b < 65536 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec2 (a * 256 + b) = a ^^^ b
    as_aux_lemma =>
      simp only [spec2,
        q,
        r,
        show a * 256 + b < 65536 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec3 (a * 256 + b) = 0
    as_aux_lemma =>
      simp only [spec3,
        show a * 256 + b < 344064 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec4 (a * 256 + b) = 0
    as_aux_lemma =>
      simp only [spec4,
        show a * 256 + b < 589824 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec5 (a * 256 + b) = 4
    as_aux_lemma =>
      simp only [spec5,
        show a * 256 + b < 65536 by as_aux_lemma => omega,
        ↓reduceIte]

/-- A row of tag 19 has its formula index. -/
private theorem row_of_tag19 {a b c d e : Nat} (facts : RowFacts 19 a b c d e) :
  ∃ i < 1048576, formulaRow i = #v[a, b, c, d, e, 19] := by
  simp only [RowFacts] at facts
  obtain ⟨ha, hb, rfl, rfl, rfl⟩ := facts
  refine ⟨65536 + (a * 128 + b), by as_aux_lemma => omega, ?_⟩
  have q : (65536 + (a * 128 + b) - 65536) / 128 = a := by as_aux_lemma => omega
  have r : (65536 + (a * 128 + b) - 65536) % 128 = b := by as_aux_lemma => omega
  apply Vector.ext
  intro j hj
  interval_cases j
  · change spec0 (65536 + (a * 128 + b)) = a
    as_aux_lemma =>
      simp only [spec0,
        q,
        show ¬ 65536 + (a * 128 + b) < 65536 by as_aux_lemma => omega,
        show 65536 + (a * 128 + b) < 81920 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec1 (65536 + (a * 128 + b)) = b
    as_aux_lemma =>
      simp only [spec1,
        r,
        show ¬ 65536 + (a * 128 + b) < 65536 by as_aux_lemma => omega,
        show 65536 + (a * 128 + b) < 81920 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec2 (65536 + (a * 128 + b)) = a ^^^ b
    as_aux_lemma =>
      simp only [spec2,
        q,
        r,
        show ¬ 65536 + (a * 128 + b) < 65536 by as_aux_lemma => omega,
        show 65536 + (a * 128 + b) < 81920 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec3 (65536 + (a * 128 + b)) = 0
    as_aux_lemma =>
      simp only [spec3,
        show 65536 + (a * 128 + b) < 344064 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec4 (65536 + (a * 128 + b)) = 0
    as_aux_lemma =>
      simp only [spec4,
        show 65536 + (a * 128 + b) < 589824 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec5 (65536 + (a * 128 + b)) = 19
    as_aux_lemma =>
      simp only [spec5,
        show ¬ 65536 + (a * 128 + b) < 65536 by as_aux_lemma => omega,
        show 65536 + (a * 128 + b) < 81920 by as_aux_lemma => omega,
        ↓reduceIte]

/-- A row of tag 20 has its formula index. -/
private theorem row_of_tag20 {a b c d e : Nat} (facts : RowFacts 20 a b c d e) :
  ∃ i < 1048576, formulaRow i = #v[a, b, c, d, e, 20] := by
  simp only [RowFacts] at facts
  obtain ⟨ha, hb, rfl, rfl, rfl⟩ := facts
  refine ⟨81920 + (a * 512 + b), by as_aux_lemma => omega, ?_⟩
  have q : (81920 + (a * 512 + b) - 81920) / 512 = a := by as_aux_lemma => omega
  have r : (81920 + (a * 512 + b) - 81920) % 512 = b := by as_aux_lemma => omega
  apply Vector.ext
  intro j hj
  interval_cases j
  · change spec0 (81920 + (a * 512 + b)) = a
    as_aux_lemma =>
      simp only [spec0,
        q,
        show ¬ 81920 + (a * 512 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 81920 + (a * 512 + b) < 81920 by as_aux_lemma => omega,
        show 81920 + (a * 512 + b) < 344064 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec1 (81920 + (a * 512 + b)) = b
    as_aux_lemma =>
      simp only [spec1,
        r,
        show ¬ 81920 + (a * 512 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 81920 + (a * 512 + b) < 81920 by as_aux_lemma => omega,
        show 81920 + (a * 512 + b) < 344064 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec2 (81920 + (a * 512 + b)) = a ^^^ b
    as_aux_lemma =>
      simp only [spec2,
        q,
        r,
        show ¬ 81920 + (a * 512 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 81920 + (a * 512 + b) < 81920 by as_aux_lemma => omega,
        show 81920 + (a * 512 + b) < 344064 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec3 (81920 + (a * 512 + b)) = 0
    as_aux_lemma =>
      simp only [spec3,
        show 81920 + (a * 512 + b) < 344064 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec4 (81920 + (a * 512 + b)) = 0
    as_aux_lemma =>
      simp only [spec4,
        show 81920 + (a * 512 + b) < 589824 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec5 (81920 + (a * 512 + b)) = 20
    as_aux_lemma =>
      simp only [spec5,
        show ¬ 81920 + (a * 512 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 81920 + (a * 512 + b) < 81920 by as_aux_lemma => omega,
        show 81920 + (a * 512 + b) < 344064 by as_aux_lemma => omega,
        ↓reduceIte]

/-- A row of tag 55 has its formula index. -/
private theorem row_of_tag55 {a b c d e : Nat} (facts : RowFacts 55 a b c d e) :
  ∃ i < 1048576, formulaRow i = #v[a, b, c, d, e, 55] := by
  simp only [RowFacts] at facts
  obtain ⟨ha, hb, hc, rfl, rfl⟩ := facts
  refine ⟨344064 + (c * 65536 + a * 256 + b), by as_aux_lemma => omega, ?_⟩
  have q : (344064 + (c * 65536 + a * 256 + b) - 344064) % 65536 / 256 = a := by as_aux_lemma => omega
  have r : (344064 + (c * 65536 + a * 256 + b) - 344064) % 256 = b := by as_aux_lemma => omega
  have s : (344064 + (c * 65536 + a * 256 + b) - 344064) / 65536 = c := by as_aux_lemma => omega
  apply Vector.ext
  intro j hj
  interval_cases j
  · change spec0 (344064 + (c * 65536 + a * 256 + b)) = a
    as_aux_lemma =>
      simp only [spec0,
        q,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 81920 by as_aux_lemma => omega,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 344064 by as_aux_lemma => omega,
        show 344064 + (c * 65536 + a * 256 + b) < 540672 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec1 (344064 + (c * 65536 + a * 256 + b)) = b
    as_aux_lemma =>
      simp only [spec1,
        r,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 81920 by as_aux_lemma => omega,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 344064 by as_aux_lemma => omega,
        show 344064 + (c * 65536 + a * 256 + b) < 540672 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec2 (344064 + (c * 65536 + a * 256 + b)) = c
    as_aux_lemma =>
      simp only [spec2,
        s,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 81920 by as_aux_lemma => omega,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 344064 by as_aux_lemma => omega,
        show 344064 + (c * 65536 + a * 256 + b) < 540672 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec3 (344064 + (c * 65536 + a * 256 + b)) = a ^^^ b
    as_aux_lemma =>
      simp only [spec3,
        q,
        r,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 344064 by as_aux_lemma => omega,
        show 344064 + (c * 65536 + a * 256 + b) < 540672 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec4 (344064 + (c * 65536 + a * 256 + b)) = 0
    as_aux_lemma =>
      simp only [spec4,
        show 344064 + (c * 65536 + a * 256 + b) < 589824 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec5 (344064 + (c * 65536 + a * 256 + b)) = 55
    as_aux_lemma =>
      simp only [spec5,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 81920 by as_aux_lemma => omega,
        show ¬ 344064 + (c * 65536 + a * 256 + b) < 344064 by as_aux_lemma => omega,
        show 344064 + (c * 65536 + a * 256 + b) < 540672 by as_aux_lemma => omega,
        ↓reduceIte]

/-- A row of tag 56 has its formula index. -/
private theorem row_of_tag56 {a b c d e : Nat} (facts : RowFacts 56 a b c d e) :
  ∃ i < 1048576, formulaRow i = #v[a, b, c, d, e, 56] := by
  simp only [RowFacts] at facts
  obtain ⟨ha, hb, hc, rfl, rfl⟩ := facts
  refine ⟨540672 + (c * 16384 + a * 128 + b), by as_aux_lemma => omega, ?_⟩
  have q : (540672 + (c * 16384 + a * 128 + b) - 540672) % 16384 / 128 = a := by as_aux_lemma => omega
  have r : (540672 + (c * 16384 + a * 128 + b) - 540672) % 128 = b := by as_aux_lemma => omega
  have s : (540672 + (c * 16384 + a * 128 + b) - 540672) / 16384 = c := by as_aux_lemma => omega
  apply Vector.ext
  intro j hj
  interval_cases j
  · change spec0 (540672 + (c * 16384 + a * 128 + b)) = a
    as_aux_lemma =>
      simp only [spec0,
        q,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 81920 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 344064 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 540672 by as_aux_lemma => omega,
        show 540672 + (c * 16384 + a * 128 + b) < 589824 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec1 (540672 + (c * 16384 + a * 128 + b)) = b
    as_aux_lemma =>
      simp only [spec1,
        r,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 81920 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 344064 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 540672 by as_aux_lemma => omega,
        show 540672 + (c * 16384 + a * 128 + b) < 589824 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec2 (540672 + (c * 16384 + a * 128 + b)) = c
    as_aux_lemma =>
      simp only [spec2,
        s,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 81920 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 344064 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 540672 by as_aux_lemma => omega,
        show 540672 + (c * 16384 + a * 128 + b) < 589824 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec3 (540672 + (c * 16384 + a * 128 + b)) = a ^^^ b
    as_aux_lemma =>
      simp only [spec3,
        q,
        r,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 344064 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 540672 by as_aux_lemma => omega,
        show 540672 + (c * 16384 + a * 128 + b) < 589824 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec4 (540672 + (c * 16384 + a * 128 + b)) = 0
    as_aux_lemma =>
      simp only [spec4,
        show 540672 + (c * 16384 + a * 128 + b) < 589824 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec5 (540672 + (c * 16384 + a * 128 + b)) = 56
    as_aux_lemma =>
      simp only [spec5,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 65536 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 81920 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 344064 by as_aux_lemma => omega,
        show ¬ 540672 + (c * 16384 + a * 128 + b) < 540672 by as_aux_lemma => omega,
        show 540672 + (c * 16384 + a * 128 + b) < 589824 by as_aux_lemma => omega,
        ↓reduceIte]

/-- A row of tag 57 has its formula index. -/
private theorem row_of_tag57 {a b c d e : Nat} (facts : RowFacts 57 a b c d e) :
  ∃ i < 1048576, formulaRow i = #v[a, b, c, d, e, 57] := by
  simp only [RowFacts] at facts
  obtain ⟨ha, hb, hc, hd, rfl⟩ := facts
  refine ⟨589824 + (a * 1024 + b * 128 + c * 8 + d), by as_aux_lemma => omega, ?_⟩
  have q0 : (589824 + (a * 1024 + b * 128 + c * 8 + d) - 589824) / 1024 = a := by as_aux_lemma => omega
  have q1 : (589824 + (a * 1024 + b * 128 + c * 8 + d) - 589824) / 128 % 8 = b := by as_aux_lemma => omega
  have q2 : (589824 + (a * 1024 + b * 128 + c * 8 + d) - 589824) / 8 % 16 = c := by as_aux_lemma => omega
  have q3 : (589824 + (a * 1024 + b * 128 + c * 8 + d) - 589824) % 8 = d := by as_aux_lemma => omega
  apply Vector.ext
  intro j hj
  interval_cases j
  · change spec0 (589824 + (a * 1024 + b * 128 + c * 8 + d)) = a
    as_aux_lemma =>
      simp only [spec0,
        q0,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 65536 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 81920 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 344064 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 540672 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 589824 by as_aux_lemma => omega,
        show 589824 + (a * 1024 + b * 128 + c * 8 + d) < 606208 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec1 (589824 + (a * 1024 + b * 128 + c * 8 + d)) = b
    as_aux_lemma =>
      simp only [spec1,
        q1,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 65536 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 81920 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 344064 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 540672 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 589824 by as_aux_lemma => omega,
        show 589824 + (a * 1024 + b * 128 + c * 8 + d) < 606208 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec2 (589824 + (a * 1024 + b * 128 + c * 8 + d)) = c
    as_aux_lemma =>
      simp only [spec2,
        q2,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 65536 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 81920 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 344064 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 540672 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 589824 by as_aux_lemma => omega,
        show 589824 + (a * 1024 + b * 128 + c * 8 + d) < 606208 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec3 (589824 + (a * 1024 + b * 128 + c * 8 + d)) = d
    as_aux_lemma =>
      simp only [spec3,
        q3,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 344064 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 540672 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 589824 by as_aux_lemma => omega,
        show 589824 + (a * 1024 + b * 128 + c * 8 + d) < 606208 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec4 (589824 + (a * 1024 + b * 128 + c * 8 + d)) = (a ^^^ c) ||| ((b ^^^ d) <<< 4)
    as_aux_lemma =>
      simp only [spec4,
        q0,
        q1,
        q2,
        q3,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 589824 by as_aux_lemma => omega,
        show 589824 + (a * 1024 + b * 128 + c * 8 + d) < 606208 by as_aux_lemma => omega,
        ↓reduceIte]
  · change spec5 (589824 + (a * 1024 + b * 128 + c * 8 + d)) = 57
    as_aux_lemma =>
      simp only [spec5,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 65536 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 81920 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 344064 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 540672 by as_aux_lemma => omega,
        show ¬ 589824 + (a * 1024 + b * 128 + c * 8 + d) < 589824 by as_aux_lemma => omega,
        show 589824 + (a * 1024 + b * 128 + c * 8 + d) < 606208 by as_aux_lemma => omega,
        ↓reduceIte]

/-- Every row meaning is a formula row. -/
theorem row_of_facts {t a b c d e : Nat} (facts : RowFacts t a b c d e) :
    ∃ i < 1048576, formulaRow i = #v[a, b, c, d, e, t] := by
  unfold RowFacts at facts
  split at facts
  · exact row_of_tag4 facts
  · exact row_of_tag19 facts
  · exact row_of_tag20 facts
  · exact row_of_tag55 facts
  · exact row_of_tag56 facts
  · exact row_of_tag57 facts
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

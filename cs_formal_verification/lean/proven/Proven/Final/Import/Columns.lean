module
public import Human.Import.Columns
public import Std.Data.TreeMap.Lemmas

@[expose] public section

namespace Airbender

private theorem GKRAddress.key_eq_iff {a b : GKRAddress} : a.key = b.key ↔ a = b := by
  constructor
  · intro h
    cases a <;> rename_i x <;> try cases x
    all_goals (cases b <;> rename_i y <;> try cases y)
    all_goals simp_all [GKRAddress.key]
  · rintro rfl; rfl

private theorem placements_foldl (l : List (Nat × GKRAddress)) (m : Std.TreeMap (List Nat) (List Nat))
    (a : GKRAddress) :
    (l.foldl (fun m (v, a) => m.alter a.key fun vs => some (v :: vs.getD [])) m).getD a.key [] =
      ((l.filter (·.2 == a)).map (·.1)).reverse ++ m.getD a.key [] := by
  induction l generalizing m with
  | nil => simp
  | cons x l ih =>
    obtain ⟨v, b⟩ := x
    rw [List.foldl_cons, ih, Std.TreeMap.getD_alter]
    by_cases h : b = a
    · subst h
      simp [Std.TreeMap.getD_eq_getD_getElem?]
    · have hk : compare b.key a.key ≠ .eq := by
        rw [Ne, Std.LawfulEqCmp.compare_eq_iff_eq]; exact fun e => h (GKRAddress.key_eq_iff.mp e)
      simp [hk, h]

/-- `Circuit.placements` holds, for each address, the variables placed there. -/
theorem placements_claim : PlacementsClaim := by
  intro c a
  rw [Circuit.placements, placements_foldl]
  simp

end Airbender

module
public import Slop.Delegation.RVCallLink

@[expose] public section

/-! The delegate link for a span of calls of different kinds (`RV.calls ks`, e.g. `RV.f1600Calls`): the list-indexed
    sibling of `calls_replicate_link`. -/

namespace Airbender.Delegation.Proofs
set_option warningAsError true

/-- A span of calls `ks`: if call `m`, from the chronological circuit state `chron m` (at any PC), is the spec's call
    `ks[m]` landing on `chron (m + 1)`, then the spec's run of `ks` from `chron 0` is `chron ks.length` with the
    spec's PC. -/
theorem calls_list_link {ks : List RV.DelegationKind} (chron : Nat → RV.State)
    (step : ∀ (m : Nat) (bound : m < ks.length), ∀ x, ∃ U, RV.calls [ks[m]] ((chron m).setPC x) = some U ∧
      RV.Same U ((chron (m + 1)).setPC (x + 4))) :
    ∃ s', RV.calls ks (chron 0) = some s' ∧
      RV.Same s' ((chron ks.length).setPC ((chron 0).pc + BitVec.ofNat 32 (4 * ks.length))) := by
  have general : ∀ m ≤ ks.length, ∃ s', RV.calls (ks.take m) (chron 0) = some s' ∧
      RV.Same s' ((chron m).setPC ((chron 0).pc + BitVec.ofNat 32 (4 * m))) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨chron 0, rfl, ?_⟩
      have : (chron 0).setPC ((chron 0).pc + BitVec.ofNat 32 (4 * 0)) = chron 0 := by
        simp [RV.State.setPC]
      rw [this]
      exact RV.Same.refl _
    | succ m ih =>
      intro bound
      obtain ⟨s', run, same⟩ := ih (by omega)
      obtain ⟨U, call, landing⟩ := step m (by omega) ((chron 0).pc + BitVec.ofNat 32 (4 * m))
      obtain ⟨U', call', sameU⟩ := calls_same same.symm call
      refine ⟨U', ?_, ?_⟩
      · rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, RV.calls_append, run,
          Option.bind_some]
        exact call'
      · rw [← pc_step]
        exact sameU.symm.trans landing
  obtain ⟨s', run, same⟩ := general ks.length (le_refl _)
  exact ⟨s', by simpa only [List.take_length] using run, same⟩

end Airbender.Delegation.Proofs

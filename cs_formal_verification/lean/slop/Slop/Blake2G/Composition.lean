import Slop.Blake2G.State

namespace Airbender.Blake2G.State.Proofs

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def project (state : Vector Arithmetic.Word 16) (a b c d : Fin 16) : Words :=
  ⟨state[a], state[b], state[c], state[d]⟩

def update (state : Vector Arithmetic.Word 16) (a b c d : Fin 16) (output : Words) :
    Vector Arithmetic.Word 16 :=
  (((state.set a output.a).set b output.b).set c output.c).set d output.d

/-- Lift the shared four-word G claim to a state update at distinct lanes.
    The other lanes are preserved, using the existing Clean reference lemmas. -/
theorem reference_update (state : Vector Arithmetic.Word 16) (a b c d : Fin 16)
    (mx my : Arithmetic.Word) (output : Words)
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d)
    (correct : Blake2G.spec ⟨project state a b c d, mx, my⟩ output) :
    (update state a b c d output).map Arithmetic.Word.value =
      Specs.BLAKE3.g (state.map Arithmetic.Word.value) a b c d mx.value my.value := by
  have selected := reference_selected (state.map Arithmetic.Word.value) a b c d mx.value my.value
    ab ac ad bc bd cd
  simp only [Blake2G.spec, project] at correct
  simp only [Fin.getElem_fin, Vector.getElem_map] at selected
  have different : a.val ≠ b.val ∧ a.val ≠ c.val ∧ a.val ≠ d.val ∧
      b.val ≠ c.val ∧ b.val ≠ d.val ∧ c.val ≠ d.val := by
    repeat' apply And.intro
    all_goals intro equal
    all_goals first
      | exact ab (Fin.ext equal) | exact ac (Fin.ext equal) | exact ad (Fin.ext equal)
      | exact bc (Fin.ext equal) | exact bd (Fin.ext equal) | exact cd (Fin.ext equal)
  apply Vector.ext
  intro i hi
  by_cases ia : i = a.val
  · subst i
    simpa [update, Vector.getElem_set, Fin.getElem_fin,
      Ne.symm different.1, Ne.symm different.2.1, Ne.symm different.2.2.1] using
      correct.1.trans selected.1.symm
  by_cases ib : i = b.val
  · subst i
    simpa [update, Vector.getElem_set, Fin.getElem_fin,
      Ne.symm different.2.2.2.1, Ne.symm different.2.2.2.2.1] using
      correct.2.1.trans selected.2.1.symm
  by_cases ic : i = c.val
  · subst i
    simpa [update, Vector.getElem_set, Fin.getElem_fin,
      Ne.symm different.2.2.2.2.2] using
      correct.2.2.1.trans selected.2.2.1.symm
  by_cases id : i = d.val
  · subst i
    simpa [update, Vector.getElem_set, Fin.getElem_fin] using
      correct.2.2.2.trans selected.2.2.2.symm
  have untouched := reference_untouched (state.map Arithmetic.Word.value) a b c d ⟨i, hi⟩
    mx.value my.value (fun eq => ia (congrArg Fin.val eq)) (fun eq => ib (congrArg Fin.val eq))
    (fun eq => ic (congrArg Fin.val eq)) (fun eq => id (congrArg Fin.val eq))
  simpa [update, Fin.getElem_fin, Vector.getElem_set,
    Ne.symm ia, Ne.symm ib, Ne.symm ic, Ne.symm id] using untouched.symm

end Airbender.Blake2G.State.Proofs

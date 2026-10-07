import Airbender.Review.Blake2G.Model
import Airbender.Proofs.Blake2G.SecondHalf


namespace Airbender.Blake2G.Proofs

set_option maxHeartbeats 1200000

/-- Unfold the existing Clean reference once over plain natural numbers.
    Circuit proofs reuse this lemma instead of reducing vector updates again. -/
theorem reference_components (a b c d mx my : Nat) :
    let a1 := add32 a (add32 b mx)
    let d1 := rotRight32 (d ^^^ a1) 16
    let c1 := add32 c d1
    let b1 := rotRight32 (b ^^^ c1) 12
    let a2 := add32 a1 (add32 b1 my)
    let d2 := rotRight32 (d1 ^^^ a2) 8
    let c2 := add32 c1 d2
    let b2 := rotRight32 (b1 ^^^ c2) 7
    let initial := #v[a, b, c, d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    let result := Specs.BLAKE3.g initial ⟨0, by decide⟩ ⟨1, by decide⟩
      ⟨2, by decide⟩ ⟨3, by decide⟩ mx my
    result[0] = a2 ∧ result[1] = b2 ∧ result[2] = c2 ∧ result[3] = d2 := by
  norm_num only [Specs.BLAKE3.g, Fin.getElem_fin, Fin.val_mk,
    Vector.getElem_set, Vector.getElem_mk]
  simp only [↓reduceIte, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  exact ⟨True.intro, True.intro, True.intro, True.intro⟩


theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    (control : Fin 512 → Vector Nat 7) :
    (circuitModel (p := p) control).SoundnessUnder (InterfaceAssumptions (p := p)) spec := by
  intro input output w ⟨interface, holds, mapping⟩
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints (setupTable control)) at holds
  rcases input with ⟨state, mx, my⟩
  rcases mapping with ⟨reads, messageX, messageY, writes⟩
  cases reads
  cases messageX
  cases messageY
  cases writes
  have firstA := first_addition hp compatible (control := control) (w := w) holds interface.aBound interface.messageXBound
  have firstD := (first_rotation (by omega) compatible (control := control) (w := w) holds).2.2.2
  have firstC := first_c_addition hp compatible (control := control) (w := w) holds interface.cBound
  have firstB := (first_rotation12 (by omega) compatible (control := control) (w := w) holds).2.2.2
  have secondA := second_addition hp compatible (control := control) (w := w) holds interface.messageYBound
  have secondD := (second_rotation (by omega) compatible (control := control) (w := w) holds).2.2
  have secondC := second_c_addition hp compatible (control := control) (w := w) holds
  have secondB := (second_rotation7 (by omega) compatible (control := control) (w := w) holds).2.2
  obtain ⟨aOutput, bOutput, cOutput, dOutput⟩ := mixing_outputs (by omega) compatible (control := control) (w := w) holds
  let a0 := Arithmetic.Word.mk (w 15).val (w 16).val
  let b0 := Arithmetic.Word.mk (w 19).val (w 20).val
  let c0 := Arithmetic.Word.mk (w 23).val (w 24).val
  let d0 := Arithmetic.Word.mk (w 27).val (w 28).val
  have native := reference_components a0.value b0.value c0.value d0.value
    (Arithmetic.Word.mk (w 33).val (w 34).val).value
    (Arithmetic.Word.mk (w 35).val (w 36).val).value
  have d1Spec := firstD.trans (congrArg (fun a : Nat => rotRight32 (d0.value ^^^ a) 16) firstA)
  have c1Spec := firstC.trans (congrArg (add32 c0.value) d1Spec)
  have b1Spec := firstB.trans (congrArg (fun c : Nat => rotRight32 (b0.value ^^^ c) 12) c1Spec)
  have a2Spec := secondA.trans (congrArg₂ (fun a b : Nat =>
    add32 a (add32 b (Arithmetic.Word.mk (w 35).val (w 36).val).value)) firstA b1Spec)
  have d2Spec := secondD.trans (congrArg₂ (fun d a : Nat => rotRight32 (d ^^^ a) 8) d1Spec a2Spec)
  have c2Spec := secondC.trans (congrArg₂ add32 c1Spec d2Spec)
  have b2Spec := secondB.trans (congrArg₂ (fun b c : Nat => rotRight32 (b ^^^ c) 7) b1Spec c2Spec)
  have aFinal := (congrArg Arithmetic.Word.value aOutput).trans a2Spec
  have bFinal := (congrArg Arithmetic.Word.value bOutput).trans b2Spec
  have cFinal := (congrArg Arithmetic.Word.value cOutput).trans c2Spec
  have dFinal := (congrArg Arithmetic.Word.value dOutput).trans d2Spec
  exact ⟨aFinal.trans native.1.symm, bFinal.trans native.2.1.symm,
    cFinal.trans native.2.2.1.symm, dFinal.trans native.2.2.2.symm⟩

end Airbender.Blake2G.Proofs

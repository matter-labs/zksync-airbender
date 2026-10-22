import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Circuits.Blake2G.State
import Airbender.Proofs.Blake2G.Soundness
import Airbender.Proofs.Blake2G.Control

namespace Airbender.Blake2G.State.Proofs

set_option maxHeartbeats 800000

/-- Reuse the actual Clean G definition at arbitrary distinct lanes. This
    connects the existing four-word claim to the full state, once for all users. -/
theorem reference_selected (state : Vector Nat 16) (a b c d : Fin 16) (mx my : Nat)
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) :
    let projected := #v[state[a], state[b], state[c], state[d],
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    let projectedResult := Specs.BLAKE3.g projected ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ mx my
    let full := Specs.BLAKE3.g state a b c d mx my
    full[a] = projectedResult[0] ∧ full[b] = projectedResult[1] ∧ full[c] = projectedResult[2] ∧ full[d] = projectedResult[3] := by
  have different : a.val ≠ b.val ∧ a.val ≠ c.val ∧ a.val ≠ d.val ∧
      b.val ≠ c.val ∧ b.val ≠ d.val ∧ c.val ≠ d.val := by
    repeat' apply And.intro
    all_goals intro equal
    all_goals first
      | exact ab (Fin.ext equal)
      | exact ac (Fin.ext equal)
      | exact ad (Fin.ext equal)
      | exact bc (Fin.ext equal)
      | exact bd (Fin.ext equal)
      | exact cd (Fin.ext equal)
  norm_num only [Specs.BLAKE3.g, Fin.getElem_fin, Fin.val_mk,
    Vector.getElem_set, Vector.getElem_mk]
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    Ne.symm different.1, Ne.symm different.2.1, Ne.symm different.2.2.1,
    Ne.symm different.2.2.2.1, Ne.symm different.2.2.2.2.1, Ne.symm different.2.2.2.2.2,
    ↓reduceIte]
  exact ⟨True.intro, True.intro, True.intro, True.intro⟩

theorem reference_untouched (state : Vector Nat 16) (a b c d i : Fin 16) (mx my : Nat)
    (ia : i ≠ a) (ib : i ≠ b) (ic : i ≠ c) (id : i ≠ d) :
    (Specs.BLAKE3.g state a b c d mx my)[i] = state[i] := by
  have different : i.val ≠ a.val ∧ i.val ≠ b.val ∧ i.val ≠ c.val ∧ i.val ≠ d.val := by
    repeat' apply And.intro
    all_goals intro equal
    all_goals first
      | exact ia (Fin.ext equal)
      | exact ib (Fin.ext equal)
      | exact ic (Fin.ext equal)
      | exact id (Fin.ext equal)
  simp only [Specs.BLAKE3.g, Fin.getElem_fin, Vector.getElem_set,
    Ne.symm different.1, Ne.symm different.2.1,
    Ne.symm different.2.2.1, Ne.symm different.2.2.2, ↓reduceIte]

theorem selected_distinct {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    {input : Input} {output : Output} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (mapping : Mapping input output w) (active : w Variables.execute = 1)
    (bound : (w Variables.controlReadLo).val < 256) :
    input.lanes.toList.Pairwise (· ≠ ·) := by
  let controller : Control.Input := ⟨⟨(w 3).val, bound⟩, true⟩
  let controlOutput : Control.Output :=
    ⟨⟨(w 5).val, (w 6).val⟩,
      Variables.stateOffsetColumns.map (fun column => (w column).val),
      Variables.messageOffsetColumns.map (fun column => (w column).val)⟩
  have controlMapping : Control.Mapping controller controlOutput w := ⟨rfl, active, rfl⟩
  have enforced := Control.Proofs.soundness hp controller controlOutput w ⟨h, controlMapping⟩
  have laneValues : input.lanes.map Fin.val = (Control.step controller).stateOffsets := by
    apply Vector.ext
    intro i hi
    have selected := mapping.laneSelection ⟨i, hi⟩
    have columns : (w Variables.stateOffsetColumns[(⟨i, hi⟩ : Fin 4)]).val =
        (Control.step controller).stateOffsets[i] := by
      have equation := congrArg (fun o : Control.Output => o.stateOffsets[i]) enforced
      interval_cases i <;> simpa [controlOutput] using equation
    simpa only [Fin.getElem_fin, Vector.getElem_map] using selected.symm.trans columns
  have computed := Control.Proofs.active_state_distinct controller rfl
  rw [← laneValues, Vector.toList_map, List.pairwise_map] at computed
  apply computed.imp
  intro left right different same
  exact different (congrArg Fin.val same)

theorem soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 262144)
    (compatible : SerializedInverse.Scale64 p) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec := by
  intro input output w relation
  obtain ⟨interface, constraints, mapping⟩ := relation
  have mixing := Airbender.Blake2G.Proofs.soundness hp compatible Control.controllerRows
    (mixingInput input) (mixingOutput input output) w ⟨interface.inputs, constraints, mapping.words⟩
  have distinct := selected_distinct (by omega) constraints mapping interface.active interface.controlBound
  have ab : input.lanes[0] ≠ input.lanes[1] := by
    exact (List.pairwise_iff_getElem.mp distinct) 0 1 (by simp) (by simp) (by decide)
  have ac : input.lanes[0] ≠ input.lanes[2] := by
    exact (List.pairwise_iff_getElem.mp distinct) 0 2 (by simp) (by simp) (by decide)
  have ad : input.lanes[0] ≠ input.lanes[3] := by
    exact (List.pairwise_iff_getElem.mp distinct) 0 3 (by simp) (by simp) (by decide)
  have bc : input.lanes[1] ≠ input.lanes[2] := by
    exact (List.pairwise_iff_getElem.mp distinct) 1 2 (by simp) (by simp) (by decide)
  have bd : input.lanes[1] ≠ input.lanes[3] := by
    exact (List.pairwise_iff_getElem.mp distinct) 1 3 (by simp) (by simp) (by decide)
  have cd : input.lanes[2] ≠ input.lanes[3] := by
    exact (List.pairwise_iff_getElem.mp distinct) 2 3 (by simp) (by simp) (by decide)
  have selected := reference_selected (input.state.map Arithmetic.Word.value)
    input.lanes[0] input.lanes[1] input.lanes[2] input.lanes[3] input.mx.value input.my.value ab ac ad bc bd cd
  simp only [Blake2G.spec, mixingInput, mixingOutput, Fin.getElem_fin] at mixing
  simp only [Fin.getElem_fin, Vector.getElem_map] at selected
  have a := mixing.1.trans selected.1.symm
  have b := mixing.2.1.trans selected.2.1.symm
  have c := mixing.2.2.1.trans selected.2.2.1.symm
  have d := mixing.2.2.2.trans selected.2.2.2.symm
  unfold spec
  apply Vector.ext
  intro i hi
  let lane : Fin 16 := ⟨i, hi⟩
  by_cases ha : lane = input.lanes[0]
  · simpa [lane, ← ha, mixingInput, mixingOutput] using a
  by_cases hb : lane = input.lanes[1]
  · simpa [lane, ← hb, mixingInput, mixingOutput] using b
  by_cases hc : lane = input.lanes[2]
  · simpa [lane, ← hc, mixingInput, mixingOutput] using c
  by_cases hd : lane = input.lanes[3]
  · simpa [lane, ← hd, mixingInput, mixingOutput] using d
  have frame := interface.untouched lane (by intro j; fin_cases j <;> assumption)
  have original := reference_untouched (input.state.map Arithmetic.Word.value)
    input.lanes[0] input.lanes[1] input.lanes[2] input.lanes[3] lane input.mx.value input.my.value ha hb hc hd
  simp only [Fin.getElem_fin, Vector.getElem_map] at original
  simpa [lane] using (congrArg Arithmetic.Word.value frame).trans original.symm

end Airbender.Blake2G.State.Proofs

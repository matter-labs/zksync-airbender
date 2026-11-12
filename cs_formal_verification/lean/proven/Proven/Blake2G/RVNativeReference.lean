module
public import Proven.Blake2G.RVNativeSpec
public import Proven.Blake2G.RVWorkVector

@[expose] public section
namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
open Blake2Round.Proofs (rv_block_words)
attribute [local irreducible] Specs.BLAKE3.g
set_option backward.isDefEq.respectTransparency false

/-- The native byte state interface uses the same reference G as its selected scheduled call. -/
theorem native_physical_reference (register : Fin 256) {before after : RV.State} {state message : RV.Word}
    (correct : Blake2G.State.spec (rvPhysicalInput ⟨register, true⟩ before state message)
      (rvPhysicalWords after state)) :
    (rvPhysicalWords after state).map Word.toBitVec =
      RV.gStep (RV.readWords before.mem message 16) (nativeIndex register) (RV.readWords before.mem state 16) := by
  have offsets := native_controller_offsets register
  have inputs : rvPhysicalInput ⟨register, true⟩ before state message =
      rvPhysicalInput (controllerAt (nativeReduced register) (nativeIndex register)) before state message := by
    simp only [rvPhysicalInput, stateLanes, offsets.1, offsets.2]
  rw [inputs] at correct
  have reference := rv_physical_reference_step (nativeReduced register) (nativeIndex register) correct
  have bounded (pointer : RV.Word) : ∀ i : Fin 16, (rvPhysicalWords before pointer)[i].Bounded := by
    intro i
    simp only [rvPhysicalWords, rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn, rvRamEncoding]
    exact Word.ofBitVec_bound _
  have step := step_gStep (nativeReduced register) (native_index_bound register)
    (rvPhysicalWords before message) (rvPhysicalWords before state) (bounded message) (bounded state)
  rw [rv_block_words, rv_block_words, ← reference] at step
  have encoded : (rvPhysicalWords after state).map Word.toBitVec =
      ((rvPhysicalWords after state).map Word.value).map (BitVec.ofNat 32) := by
    apply Vector.ext
    intro i bound
    simp only [Vector.getElem_map, Word.toBitVec]
  exact encoded.trans step

end Airbender.Blake2G.Proofs

import Human.Trace.Workers.Blake2G.WorkVector
import Slop.Deleg.BlakeG
import Slop.Arithmetic.Word

/-! State-free agreement of the G span's reference with the spec's `G` delegation (`RV.Delegation.blakeG`): the
    pinned controller's lanes and message words are `gIndices`/`SIGMA` (`controller_indices`), the x12 schedule is
    `RV.gCtl`, and one `WorkVector.step` is `RV.gStep` on 32-bit words. -/

namespace Airbender.Blake2G.Proofs
open Arithmetic
set_option warningAsError true

theorem callCount_eq_nG (reduced : Bool) : callCount reduced = RV.nG reduced := by
  cases reduced <;> rfl

/-- The controller's lanes and message offsets for call `k` are `gIndices (k % 8)` and `SIGMA (k / 8)`. -/
theorem controller_indices : ∀ reduced : Bool, ∀ k : Fin 80, k.val < callCount reduced →
    (∀ i : Fin 4, Fin.ofNat 16 (Control.step (controllerAt reduced k.val)).stateOffsets[i] =
      RV.Delegation.gIndices ⟨k.val % 8, Nat.mod_lt _ (by decide)⟩ i) ∧
    Fin.ofNat 16 (Control.step (controllerAt reduced k.val)).messageOffsets[0] =
      Spec.SIGMA ⟨k.val / 8 % 10, Nat.mod_lt _ (by decide)⟩ ⟨2 * (k.val % 8), by omega⟩ ∧
    Fin.ofNat 16 (Control.step (controllerAt reduced k.val)).messageOffsets[1] =
      Spec.SIGMA ⟨k.val / 8 % 10, Nat.mod_lt _ (by decide)⟩ ⟨2 * (k.val % 8) + 1, by omega⟩ := by
  decide +kernel

/-- x12 before call `k` of the span is `RV.gCtl`. -/
theorem controlAt_toBitVec (reduced : Bool) {k : Nat} (bound : k < callCount reduced) :
    (controlAt reduced k).toBitVec = RV.gCtl reduced k := by
  simp only [controlAt, Word.toBitVec, Word.value, Nat.mod_eq_of_lt bound, RV.gCtl, limbBase]
  cases reduced <;> simp

/-- One reference G step is the spec's `gStep` on 32-bit words. -/
theorem step_gStep (reduced : Bool) {k : Nat} (bound : k < callCount reduced) (message state : Vector Word 16)
    (messageBound : ∀ i : Fin 16, message[i].Bounded) (stateBound : ∀ i : Fin 16, state[i].Bounded) :
    (WorkVector.step reduced k message (state.map Word.value)).map (BitVec.ofNat 32) =
      RV.gStep (message.map Word.toBitVec) k (state.map Word.toBitVec) := by
  have k80 : k < 80 := by cases reduced <;> simp [callCount] at bound <;> omega
  obtain ⟨lanes, first, second⟩ := controller_indices reduced ⟨k, k80⟩ bound
  have values : (state.map Word.toBitVec).map BitVec.toNat = state.map Word.value := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    exact Word.toBitVec_toNat (stateBound ⟨i, hi⟩)
  have messageValue (s : Fin 16) : (message.map Word.toBitVec)[s].toNat = message[s].value := by
    simp only [Fin.getElem_fin, Vector.getElem_map]
    exact Word.toBitVec_toNat (messageBound s)
  have mx : message[Fin.ofNat 16 (Control.step (controllerAt reduced k)).messageOffsets[0]].value =
      (message.map Word.toBitVec)[Spec.SIGMA ⟨k / 8 % 10, Nat.mod_lt _ (by decide)⟩
        ⟨2 * (k % 8), by omega⟩].toNat := by
    rw [messageValue, ← first]
  have my : message[Fin.ofNat 16 (Control.step (controllerAt reduced k)).messageOffsets[1]].value =
      (message.map Word.toBitVec)[Spec.SIGMA ⟨k / 8 % 10, Nat.mod_lt _ (by decide)⟩
        ⟨2 * (k % 8) + 1, by omega⟩].toNat := by
    rw [messageValue, ← second]
  simp only [WorkVector.step, RV.gStep, Spec.G, values]
  rw [lanes 0, lanes 1, lanes 2, lanes 3, mx, my]

end Airbender.Blake2G.Proofs

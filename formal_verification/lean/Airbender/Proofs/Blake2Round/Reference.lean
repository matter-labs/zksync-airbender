import Airbender.Proofs.Blake2G.Composition

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- Every lane and message index comes from the pinned Clean round definition.
def callConstants (phase : Fin 2) (call : Fin 4) :
    Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16 :=
  Specs.BLAKE3.roundConstants[4 * phase.val + call.val]

def callInput (phase : Fin 2) (call : Fin 4) (state message : Vector Arithmetic.Word 16) :
    Blake2G.Input :=
  let (a, b, c, d, mx, my) := callConstants phase call
  ⟨Blake2G.State.Proofs.project state a b c d, message[mx.val], message[my.val]⟩

def callUpdate (phase : Fin 2) (call : Fin 4) (state : Vector Arithmetic.Word 16)
    (output : Blake2G.Words) : Vector Arithmetic.Word 16 :=
  let (a, b, c, d, _, _) := callConstants phase call
  Blake2G.State.Proofs.update state a b c d output

def referenceCall (phase : Fin 2) (call : Fin 4) (state message : Vector Nat 16) : Vector Nat 16 :=
  let (a, b, c, d, mx, my) := callConstants phase call
  Specs.BLAKE3.g state a b c d message[mx.val] message[my.val]

def phaseUpdate (phase : Fin 2) (state : Vector Arithmetic.Word 16)
    (output : Fin 4 → Blake2G.Words) : Vector Arithmetic.Word 16 :=
  callUpdate phase 3 (callUpdate phase 2 (callUpdate phase 1
    (callUpdate phase 0 state (output 0)) (output 1)) (output 2)) (output 3)

def referencePhase (phase : Fin 2) (state message : Vector Nat 16) : Vector Nat 16 :=
  referenceCall phase 3 (referenceCall phase 2 (referenceCall phase 1
    (referenceCall phase 0 state message) message) message) message

private theorem distinct_lanes (phase : Fin 2) (call : Fin 4) :
    let (a, b, c, d, _, _) := callConstants phase call
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  fin_cases phase <;> fin_cases call <;> decide

theorem call_reference (phase : Fin 2) (call : Fin 4)
    (state message : Vector Arithmetic.Word 16) (output : Blake2G.Words)
    (correct : Blake2G.spec (callInput phase call state message) output) :
    (callUpdate phase call state output).map Arithmetic.Word.value =
      referenceCall phase call (state.map Arithmetic.Word.value) (message.map Arithmetic.Word.value) := by
  have distinct := distinct_lanes phase call
  dsimp only [callInput, callUpdate, referenceCall] at correct ⊢
  simpa only [Vector.getElem_map] using
    Blake2G.State.Proofs.reference_update state
      (callConstants phase call).1 (callConstants phase call).2.1
      (callConstants phase call).2.2.1 (callConstants phase call).2.2.2.1
      message[(callConstants phase call).2.2.2.2.1.val]
      message[(callConstants phase call).2.2.2.2.2.val] output
      distinct.1 distinct.2.1 distinct.2.2.1 distinct.2.2.2.1
      distinct.2.2.2.2.1 distinct.2.2.2.2.2 correct

/-- Within either phase the four calls touch disjoint lanes. -/
theorem input_after_update (phase : Fin 2) (earlier call : Fin 4)
    (before : earlier.val < call.val) (state message : Vector Arithmetic.Word 16)
    (output : Blake2G.Words) :
    callInput phase call (callUpdate phase earlier state output) message =
      callInput phase call state message := by
  fin_cases phase <;> fin_cases earlier <;> fin_cases call
  all_goals norm_num at before
  all_goals simp [callInput, callUpdate, callConstants, Specs.BLAKE3.roundConstants,
    Blake2G.State.Proofs.project, Blake2G.State.Proofs.update,
    Fin.getElem_fin]

/-- Compose four verified G calls once for both columns and diagonals. -/
theorem phase_reference (phase : Fin 2) (state message : Vector Arithmetic.Word 16)
    (output : Fin 4 → Blake2G.Words)
    (correct : ∀ call : Fin 4, Blake2G.spec (callInput phase call state message) (output call)) :
    (phaseUpdate phase state output).map Arithmetic.Word.value =
      referencePhase phase (state.map Arithmetic.Word.value) (message.map Arithmetic.Word.value) := by
  let s0 := callUpdate phase 0 state (output 0)
  let s1 := callUpdate phase 1 s0 (output 1)
  let s2 := callUpdate phase 2 s1 (output 2)
  have c0 := call_reference phase 0 state message (output 0) (correct 0)
  have h1 : Blake2G.spec (callInput phase 1 s0 message) (output 1) := by
    rw [input_after_update phase 0 1 (by decide)]
    exact correct 1
  have c1 := call_reference phase 1 s0 message (output 1) h1
  have h2 : Blake2G.spec (callInput phase 2 s1 message) (output 2) := by
    rw [input_after_update phase 1 2 (by decide), input_after_update phase 0 2 (by decide)]
    exact correct 2
  have c2 := call_reference phase 2 s1 message (output 2) h2
  have h3 : Blake2G.spec (callInput phase 3 s2 message) (output 3) := by
    rw [input_after_update phase 2 3 (by decide), input_after_update phase 1 3 (by decide),
      input_after_update phase 0 3 (by decide)]
    exact correct 3
  have c3 := call_reference phase 3 s2 message (output 3) h3
  rw [c2, c1, c0] at c3
  exact c3

theorem round_phases (state message : Vector Nat 16) :
    Specs.BLAKE3.round state message = referencePhase 1 (referencePhase 0 state message) message := rfl

end Airbender.Blake2Round.Proofs

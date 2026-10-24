import GKRProtocol.NativeLookup

namespace Tests.GKRLookupReduction
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 32768

private def pair (offset : Nat) : RationalPorts :=
  ⟨.InnerLayer 1 offset, .InnerLayer 1 (offset + 1)⟩

private def steps : List LookupStep :=
  [.seed (pair 0) 0 1,
   .copy (.InnerLayer 2 0) (pair 0).numerator,
   .copy (.InnerLayer 2 1) (pair 0).denominator,
   .extend (pair 2) ⟨.InnerLayer 2 0, .InnerLayer 2 1⟩ 2]

private def replay : Option (LookupTree Nat) := do
  let environment ← LookupStep.run steps []
  environment.pair (pair 2)

theorem follows_component_copies_and_remainder :
    replay = some (.add (.add (.leaf 0) (.leaf 1)) (.leaf 2)) := by decide +kernel

theorem rejects_swapped_pair_components :
    ((LookupStep.run steps []).bind (fun environment =>
      environment.pair ⟨(pair 2).denominator, (pair 2).numerator⟩)).isSome = false := by decide +kernel

theorem rejects_mixed_pair_components :
    ((LookupStep.run steps []).bind (fun environment =>
      environment.pair ⟨(pair 0).numerator, (pair 2).denominator⟩)).isSome = false := by decide +kernel

theorem rejects_missing_copy :
    (LookupStep.run
      [.seed (pair 0) 0 1, .copy (.InnerLayer 2 0) (pair 0).numerator,
       .extend (pair 2) ⟨.InnerLayer 2 0, .InnerLayer 2 1⟩ 2] []).isSome = false := by decide +kernel

theorem rejects_repeated_source_label :
    decide (List.Perm [0, 1, 1] [0, 1, 2]) = false := by decide +kernel

theorem rejects_dropped_source_label :
    decide (List.Perm [0, 1] [0, 1, 2]) = false := by decide +kernel

private def payload : LookupPayload := .input (.BaseLayerWitness 0)
private def native : List NativeLookupGate := [.pair (pair 0) payload payload]
private def registry : List NativeLookupLeaf := [⟨.one, payload⟩, ⟨.one, payload⟩]

theorem accepts_actual_gate_selector :
    (NativeLookupBinding.mk 0 (.seed (pair 0) 0 1)).Valid registry native := by
  exact ⟨rfl, rfl, rfl⟩

theorem rejects_unknown_gate_selector :
    ¬(NativeLookupBinding.mk 1 (.seed (pair 0) 0 1)).Valid registry native := by
  intro impossible
  exact impossible

theorem rejects_wrong_operand_weight :
    ¬(NativeLookupGate.pair (pair 0) payload payload).Normalizes
      [⟨.column (.BaseLayerWitness 0), payload⟩, ⟨.one, payload⟩] (.seed (pair 0) 0 1) := by
  intro checked
  have wrong := congrArg (fun leaf : Option NativeLookupLeaf => leaf.map NativeLookupLeaf.weight) checked.2.1
  cases wrong

end Tests.GKRLookupReduction

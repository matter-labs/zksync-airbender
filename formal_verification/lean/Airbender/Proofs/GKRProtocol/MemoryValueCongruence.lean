import Airbender.Proofs.GKRProtocol.MemoryTokens

namespace Airbender.Compiler.Source
set_option warningAsError true

theorem MemoryField.value_congr (field : MemoryField) (before after : MemoryValues)
    (original : ∀ index ∈ field.originalIndices, before.original index = after.original index)
    (history : ∀ query limb, before.readTimestamp query limb = after.readTimestamp query limb)
    (initial : before.initializationAddress = after.initializationAddress)
    (terminalTime : before.teardownTimestamp = after.teardownTimestamp)
    (terminalValue : before.teardownValue = after.teardownValue) :
    field.value before = field.value after := by
  induction field with
  | input expression =>
    cases expression with
    | Variable index => exact original index (by simp [originalIndices])
    | Expression terms constant =>
      simp only [value, LookupInput.value]
      apply congrArg (coefficientValue constant + ·)
      apply congrArg List.sum
      apply List.map_congr_left
      intro term member
      rw [original term.2 (List.mem_map.mpr ⟨term, member, rfl⟩)]
  | readTimestamp query limb => exact history query limb
  | initializationAddress limb => exact congrFun initial limb
  | teardownTimestamp query limb => exact congrFun (congrFun terminalTime query) limb
  | teardownValue query limb => exact congrFun (congrFun terminalValue query) limb
  | constant => rfl
  | add left right leftProof rightProof =>
    simp only [value]
    rw [leftProof (fun index member => original index (List.mem_append_left _ member)),
      rightProof (fun index member => original index (List.mem_append_right _ member))]
  | scale scalar inner proof => exact congrArg ((scalar : BaseField) * ·) (proof original)
  | neg inner proof => exact congrArg Neg.neg (proof original)

def MemoryField.historyIndices : MemoryField → List (Nat × Fin 2)
  | .readTimestamp query limb => [(query, limb)]
  | .add left right => left.historyIndices ++ right.historyIndices
  | .scale _ inner | .neg inner => inner.historyIndices
  | _ => []

theorem MemoryField.value_congr_scoped (field : MemoryField) (before after : MemoryValues)
    (original : ∀ index ∈ field.originalIndices, before.original index = after.original index)
    (history : ∀ index ∈ field.historyIndices,
      before.readTimestamp index.1 index.2 = after.readTimestamp index.1 index.2)
    (initial : before.initializationAddress = after.initializationAddress)
    (terminalTime : before.teardownTimestamp = after.teardownTimestamp)
    (terminalValue : before.teardownValue = after.teardownValue) :
    field.value before = field.value after := by
  induction field with
  | input expression =>
    cases expression with
    | Variable index => exact original index (by simp [originalIndices])
    | Expression terms constant =>
      simp only [value, LookupInput.value]
      apply congrArg (coefficientValue constant + ·)
      apply congrArg List.sum
      apply List.map_congr_left
      intro term member
      rw [original term.2 (List.mem_map.mpr ⟨term, member, rfl⟩)]
  | readTimestamp query limb => exact history (query, limb) (by simp [historyIndices])
  | initializationAddress limb => exact congrFun initial limb
  | teardownTimestamp query limb => exact congrFun (congrFun terminalTime query) limb
  | teardownValue query limb => exact congrFun (congrFun terminalValue query) limb
  | constant => rfl
  | add left right leftProof rightProof =>
    simp only [value]
    rw [leftProof (fun index member => original index (List.mem_append_left _ member))
      (fun index member => history index (List.mem_append_left _ member)),
      rightProof (fun index member => original index (List.mem_append_right _ member))
      (fun index member => history index (List.mem_append_right _ member))]
  | scale scalar inner proof => exact congrArg ((scalar : BaseField) * ·) (proof original history)
  | neg inner proof => exact congrArg Neg.neg (proof original history)

end Airbender.Compiler.Source

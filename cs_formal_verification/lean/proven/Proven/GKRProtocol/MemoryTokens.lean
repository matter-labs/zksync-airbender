module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemorySource
public import Proven.GKRProtocol.NativeMemoryBridge

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler
open NativeArithmetic NativeMemory NativeMemoryBridge

/-- Every raw field limb of a source memory row, in the token format of the machine arguments.
    No word bound and no sampled fingerprint equality is used. -/
def Source.MemoryRow.token (row : Source.MemoryRow) (values : Source.MemoryValues) :
    Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair (row.addressSpace.value values).val
      (Nat.pair (row.address.low.value values).val (row.address.high.value values).val),
    (row.timestamp.low.value values, row.timestamp.high.value values),
    Nat.pair (row.data.low.value values).val (row.data.high.value values).val⟩

/-- The state of a PC-state token. -/
def tokenState (token : Trace.MemoryToken babyBearModulus) : PCState.State babyBearModulus :=
  ⟨((Nat.unpair token.value).1, (Nat.unpair token.value).2), token.time⟩

theorem state_token_left_inverse (state : PCState.State babyBearModulus) :
    tokenState (stateToken state) = state := by
  cases state
  simp [tokenState, stateToken]

theorem Source.MemoryField.withOriginal_value (field : Source.MemoryField)
    (values : Source.MemoryValues) (original : Nat → Source.BaseField)
    (same : ∀ index ∈ field.originalIndices, original index = values.original index) :
    field.value {values with original := original} = field.value values := by
  induction field with
  | input expression =>
    cases expression with
    | Variable index => exact same index (by simp [originalIndices])
    | Expression terms constant =>
      simp only [value, LookupInput.value]
      apply congrArg (coefficientValue constant + ·)
      apply congrArg List.sum
      apply List.map_congr_left
      intro term member
      rw [same term.2 (List.mem_map.mpr ⟨term, member, rfl⟩)]
  | readTimestamp | initializationAddress | teardownTimestamp | teardownValue | constant => rfl
  | add left right leftProof rightProof =>
    simp only [value]
    rw [leftProof (fun index member => same index (List.mem_append_left _ member)),
      rightProof (fun index member => same index (List.mem_append_right _ member))]
  | scale scalar inner proof => exact congrArg ((scalar : Source.BaseField) * ·) (proof same)
  | neg inner proof => exact congrArg Neg.neg (proof same)

theorem Source.MemoryRow.token_congr (row : Source.MemoryRow) (before after : Source.MemoryValues)
    (same : ∀ field ∈ row.fields, field.value before = field.value after) :
    row.token before = row.token after := by
  unfold token
  rw [same row.addressSpace (by simp [fields]), same row.address.low (by simp [fields]),
    same row.address.high (by simp [fields]), same row.timestamp.low (by simp [fields]),
    same row.timestamp.high (by simp [fields]), same row.data.low (by simp [fields]),
    same row.data.high (by simp [fields])]

/-- Source rows read the same tokens from any values that agree on their original columns. -/
theorem Source.MemoryRow.tokens_original (rows : List Source.MemoryRow) (values : Source.MemoryValues)
    (original : Nat → Source.BaseField)
    (same : ∀ row ∈ rows, ∀ index ∈ row.originalIndices, original index = values.original index) :
    rows.map (fun row => row.token {values with original := original}) = rows.map (fun row => row.token values) := by
  apply List.map_congr_left
  intro row member
  apply Source.MemoryRow.token_congr
  intro field included
  apply Source.MemoryField.withOriginal_value
  intro index used
  exact same row member index (List.mem_flatMap.mpr ⟨field, included, used⟩)

variable {R : Type} [CommRing R]

/-- The native fingerprint of a source row is the encoding of its token. -/
theorem Source.MemoryRow.token_fingerprint (row : Source.MemoryRow) (values : Source.MemoryValues)
    (challenges : NativeMemory.Challenges R) :
    challenges.memory.encode (row.token values) =
      row.fingerprint values challenges.memory.embed (cacheChallenges challenges) := by
  simp only [InitsTeardowns.Native.Parameters.encode, token, Nat.unpair_pair, ZMod.natCast_zmod_val,
    fingerprint, cacheChallenges]
  rfl

theorem Source.MemoryRow.token_products (rows : List Source.MemoryRow) (values : Source.MemoryValues)
    (challenges : NativeMemory.Challenges R) :
    ((rows.map fun row => row.token values).map challenges.memory.encode).prod =
      (rows.map fun row => row.fingerprint values challenges.memory.embed (cacheChallenges challenges)).prod := by
  simp only [List.map_map, Function.comp_def, token_fingerprint]

/-- Placement agreement gives the original columns of a source memory placement. -/
theorem Source.MemoryPlacement.original_of_agreement {n : Nat} {circuit : Circuit}
    {physical : GKRAddress → F} {assignment : Nat → F}
    (placement : Source.MemoryPlacement n) (address : Fin n → GKRAddress) (indices : List Nat)
    (checked : indices.all (fun index => circuit.placement_data.entries.toList.any
      fun entry => decide (entry = (index, address (placement.original index)))) = true)
    (agreement : PlacementAgreement circuit physical assignment) :
    ∀ index ∈ indices, assignment index = (placement.project (physical ∘ address)).original index := by
  intro index member
  obtain ⟨entry, entryMember, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp checked index member)
  have equal := of_decide_eq_true same
  subst equal
  exact agreement _ (Array.mem_def.mpr entryMember)

/-- The reduced RAM outputs and the output map give the stated RAM products. -/
theorem ram_products_of_outputs {circuit : Circuit} {challenges : NativeMemory.Challenges R}
    {values : GKRAddress → R} {execute : F} {reads writes : List (Trace.MemoryToken babyBearModulus)}
    {readOutput writeOutput : GKRAddress} (outputs : ramOutputs circuit = [readOutput, writeOutput])
    (read : values readOutput = maskProduct (challenges.memory.embed execute) (reads.map challenges.memory.encode).prod)
    (write : values writeOutput = maskProduct (challenges.memory.embed execute) (writes.map challenges.memory.encode).prod) :
    RamProducts circuit challenges values execute reads writes := by
  simp only [RamProducts, outputs, List.map_cons, List.map_nil, read, write, PaddingBoundary.mask, maskProduct,
    Challenges.embed, List.cons.injEq, and_true]
  constructor <;> ring

end Airbender.Compiler

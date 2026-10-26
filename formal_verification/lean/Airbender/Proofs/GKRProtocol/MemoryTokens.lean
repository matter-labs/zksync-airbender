import Airbender.Proofs.GKRProtocol.MemorySource
import Airbender.Proofs.GKRCompiler.Reduction
import Airbender.Review.Helpers.Context.Model
import Airbender.Proofs.BabyBear

namespace Airbender.Compiler
set_option warningAsError true

/-- Preserve every raw field limb in the exact token format consumed by the
pooled execution proofs. No word bound or sampled fingerprint equality is used. -/
def Source.MemoryRow.token (row : Source.MemoryRow) (values : Source.MemoryValues) :
    Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair (row.addressSpace.value values).val
      (Nat.pair (row.address.low.value values).val (row.address.high.value values).val),
    (row.timestamp.low.value values, row.timestamp.high.value values),
    Nat.pair (row.data.low.value values).val (row.data.high.value values).val⟩

def memoryTokenFingerprint {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (token : Trace.MemoryToken babyBearModulus) : R :=
  challenges.memoryGamma + hom ((Nat.unpair token.address).1 : Source.BaseField) +
    challenges.memoryPowers ⟨0, by decide⟩ * hom ((Nat.unpair (Nat.unpair token.address).2).1 : Source.BaseField) +
    challenges.memoryPowers ⟨1, by decide⟩ * hom ((Nat.unpair (Nat.unpair token.address).2).2 : Source.BaseField) +
    challenges.memoryPowers ⟨2, by decide⟩ * hom token.time.1 +
    challenges.memoryPowers ⟨3, by decide⟩ * hom token.time.2 +
    challenges.memoryPowers ⟨4, by decide⟩ * hom ((Nat.unpair token.value).1 : Source.BaseField) +
    challenges.memoryPowers ⟨5, by decide⟩ * hom ((Nat.unpair token.value).2 : Source.BaseField)

/-- Native PC-space tuples carry PC limbs in their data and use address space
two. Execution separates their exact matching from register/RAM matching. -/
def pcStateMemoryToken (state : PCState.State babyBearModulus) : Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair 2 (Nat.pair 0 0), state.timestamp, Nat.pair state.pc.1.val state.pc.2.val⟩

@[simp] theorem pc_address_space_value : (2 : Source.BaseField).val = 2 := by decide +kernel

def memoryTokenPCState (token : Trace.MemoryToken babyBearModulus) : PCState.State babyBearModulus :=
  ⟨((Nat.unpair token.value).1, (Nat.unpair token.value).2), token.time⟩

theorem memory_pc_state_left_inverse (state : PCState.State babyBearModulus) :
    memoryTokenPCState (pcStateMemoryToken state) = state := by
  cases state
  simp [memoryTokenPCState, pcStateMemoryToken]

theorem pc_state_token_injective : Function.Injective pcStateMemoryToken :=
  Function.LeftInverse.injective memory_pc_state_left_inverse

theorem pc_state_token_matching (before after : List (PCState.State babyBearModulus))
    (matching : (before.map pcStateMemoryToken).Perm (after.map pcStateMemoryToken)) :
    before.Perm after := by
  simpa [List.map_map, Function.comp_def, memory_pc_state_left_inverse] using
    matching.map memoryTokenPCState

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

theorem Source.MemoryRow.token_congr (row : Source.MemoryRow)
    (before after : Source.MemoryValues)
    (same : ∀ field ∈ row.fields, field.value before = field.value after) :
    row.token before = row.token after := by
  unfold token
  rw [same row.addressSpace (by simp [fields]), same row.address.low (by simp [fields]),
    same row.address.high (by simp [fields]), same row.timestamp.low (by simp [fields]),
    same row.timestamp.high (by simp [fields]), same row.data.low (by simp [fields]),
    same row.data.high (by simp [fields])]

theorem Source.MemoryRow.token_fingerprint {R : Type} [CommRing R]
    (row : Source.MemoryRow) (values : Source.MemoryValues)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) :
    memoryTokenFingerprint hom challenges (row.token values) = row.fingerprint values hom challenges := by
  simp only [memoryTokenFingerprint, token, Nat.unpair_pair, ZMod.natCast_zmod_val,
    fingerprint]

theorem Source.MemoryRow.token_products {R : Type} [CommRing R]
    (rows : List Source.MemoryRow) (values : Source.MemoryValues)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) :
    ((rows.map (fun row => row.token values)).map (memoryTokenFingerprint hom challenges)).prod =
      (rows.map (fun row => row.fingerprint values hom challenges)).prod := by
  simp only [List.map_map, Function.comp_def, token_fingerprint]

theorem memory_token_permutation_products {R : Type} [CommRing R]
    (reads writes : List (Trace.MemoryToken babyBearModulus))
    (matching : reads.Perm writes) (hom : Source.BaseField →+* R)
    (challenges : CacheChallenges R) :
    (reads.map (memoryTokenFingerprint hom challenges)).prod =
      (writes.map (memoryTokenFingerprint hom challenges)).prod :=
  (matching.map (memoryTokenFingerprint hom challenges)).prod_eq

def Source.MemoryRow.activeTokens (execute : Source.BaseField)
    (rows : List Source.MemoryRow) (values : Source.MemoryValues) :
    List (Trace.MemoryToken babyBearModulus) :=
  if execute = 0 then [] else rows.map (fun row => row.token values)

theorem Source.MemoryRow.active_token_products {R : Type} [CommRing R]
    (rows : List Source.MemoryRow) (values : Source.MemoryValues)
    (execute : Source.BaseField) (boolean : execute = 0 ∨ execute = 1)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) :
    ((activeTokens execute rows values).map (memoryTokenFingerprint hom challenges)).prod =
      maskProduct (hom execute) (rows.map (fun row => row.fingerprint values hom challenges)).prod := by
  rcases boolean with inactive | active
  · simp [activeTokens, inactive, maskProduct_inactive]
  · rw [activeTokens, if_neg (by rw [active]; exact one_ne_zero), token_products,
      active, map_one, maskProduct_active]

end Airbender.Compiler

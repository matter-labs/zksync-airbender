import Airbender.Review.Circuits.Blake2Worker.MemoryKeys
import Airbender.Proofs.Blake2Worker.NativeProcessing
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Worker.MemoryKeyProofs
open Verification Native ProcessingArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem descriptors (slot : Fin 43) : keyDescriptors.size = 43 ∧
    (keyDescriptor slot).access = memoryAccess slot := by
  fin_cases slot <;> decide +kernel

private def locationProperty : KeyLocation → Prop
  | .register index => index = 10 ∨ index = 11 ∨ index = 12
  | .indirect base offset => base[0] ∈ processingMemoryColumns.toList ∧
      base[1] ∈ processingMemoryColumns.toList ∧ offset < 128

private instance locationDecidable (location : KeyLocation) : Decidable (locationProperty location) := by
  cases location <;> unfold locationProperty <;> infer_instance

theorem location_columns (slot : Fin 43) :
    match (keyDescriptor slot).location with
    | .register index => index = 10 ∨ index = 11 ∨ index = 12
    | .indirect base offset => base[0] ∈ processingMemoryColumns.toList ∧
        base[1] ∈ processingMemoryColumns.toList ∧ offset < 128 := by
  change locationProperty (keyDescriptor slot).location
  fin_cases slot <;> decide +kernel

/-- Pure address helper for derived zero inputs; no perrow range answer. -/
theorem zero_indirect (offset : Nat) (small : offset < 65536) :
    stageTwoIndirectAddress 0 0 offset = some ⟨0,offset,0⟩ := by
  simp [stageTwoIndirectAddress,Nat.mod_eq_of_lt small,Nat.div_eq_of_lt small]

theorem padding_address {w : Nat → ZMod mersenne31Modulus}
    (effects : ProcessingEffects w) (zero : w constraintsABI.multiplicity = 0) (slot : Fin 43) :
    stageTwoKeyAddress w (keyDescriptor slot).location = some (quotientKeyAddress w (keyDescriptor slot).location) := by
  have columns := location_columns slot
  cases location : (keyDescriptor slot).location with
  | register index => rfl
  | indirect base offset =>
      rw [location] at columns
      obtain ⟨lo,hi,bound⟩ := columns
      have loZero := effects.paddingMemory zero _ lo
      have hiZero := effects.paddingMemory zero _ hi
      simp only [stageTwoKeyAddress,quotientKeyAddress,loZero,hiZero,zero_add]
      exact zero_indirect offset (by omega)

theorem padding_value {w : Nat → ZMod mersenne31Modulus}
    (effects : ProcessingEffects w) (zero : w constraintsABI.multiplicity = 0) (slot : Fin 43) (write : Bool) :
    keyValue w slot write = #v[0,0] := by
  obtain ⟨_,_,r0,r1,w0,w1⟩ := effects.paddingAccesses zero slot
  cases write <;> apply Vector.ext
  all_goals
    intro i bound
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp_all [keyValue]

theorem padding_time {w : Nat → ZMod mersenne31Modulus}
    (effects : ProcessingEffects w) (zero : w constraintsABI.multiplicity = 0) (slot : Fin 43) (write : Bool) :
    keyTime w slot write = #v[0,0] := by
  have t0 : w constraintsABI.writeTime[0] = 0 := effects.paddingMemory zero _ (by decide +kernel)
  have t1 : w constraintsABI.writeTime[1] = 0 := effects.paddingMemory zero _ (by decide +kernel)
  obtain ⟨r0,r1,_⟩ := effects.paddingAccesses zero slot
  cases write <;> apply Vector.ext
  all_goals
    intro i bound
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp_all [keyTime]

theorem padding_keys {w : Nat → ZMod mersenne31Modulus} (accepted : LocalProcessingAccepted w) : PaddingMemoryKeys w := by
  have effects := ProcessingProofs.effects accepted.conventions
  refine ⟨padding_address effects,?_,?_,?_⟩
  · intro zero slot
    simp only [stageTwoMemoryKey,padding_address effects zero slot,Option.map_some,quotientMemoryKey]
  · intro zero slot
    simp only [stageTwoMemoryKey,padding_address effects zero slot,Option.map_some,quotientMemoryKey]
  · intro zero slot
    simp only [quotientMemoryKey,padding_value effects zero slot,padding_time effects zero slot]

theorem padding_products {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) {w : Nat → ZMod mersenne31Modulus}
    (accepted : LocalProcessingAccepted w) (zero : w constraintsABI.multiplicity = 0) :
    memoryKeyProduct embed ch w true = memoryKeyProduct embed ch w false := by
  have keys := (padding_keys accepted).equalKeys zero
  have same : (fun slot : Fin 43 => memoryKeyArgument embed ch (quotientMemoryKey w slot true)) =
      (fun slot : Fin 43 => memoryKeyArgument embed ch (quotientMemoryKey w slot false)) := by
    funext slot
    rw [keys slot]
  unfold memoryKeyProduct
  rw [same]

end Airbender.Blake2Worker.MemoryKeyProofs

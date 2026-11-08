import Airbender.Review.Circuits.ReducedMachine.StageTwoKeys
import Airbender.Proofs.ReducedMachine.NativeAddressSupport
import Mathlib.Tactic.FinCases

namespace Airbender.NativeStageTwoKeyProofs
open Airbender.NativeStageTwoKeys
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Entire generic cast/addition arithmetic before descriptor sampling. -/
theorem sum_value {low : F} {offset : Nat} (small : low.val < 65536) (short : offset < 128) :
    (low + (offset : F)).val = low.val + offset := by
  have room : 65536 + 128 < mersenne31Modulus := by decide +kernel
  have bound : low.val + offset < mersenne31Modulus := by omega
  have cast : low + (offset : F) = ((low.val + offset : Nat) : F) := by
    simp only [Nat.cast_add,ZMod.natCast_zmod_val]
  rw [cast,ZMod.val_natCast_of_lt bound]

theorem ram_bounds {low high : F} (domain : Airbender.NativeAddressSupport.Domain ⟨0,low,high⟩) :
    low.val < 65536 ∧ high.val < 65536 := by
  rcases domain with ⟨bad,_,_⟩ | ⟨_,lo,hi⟩
  · exact False.elim (zero_ne_one bad)
  · exact ⟨lo,hi⟩

theorem indirect_address {low high : F} {offset : Nat}
    (lo : low.val < 65536) (hi : high.val < 65536) (sum : low.val + offset < 65536) :
    stageTwoIndirectAddress low high offset = some ⟨0,low+offset,high⟩ := by
  have cast : ((low.val + offset : Nat) : F) = low + offset := by
    simp only [Nat.cast_add,ZMod.natCast_zmod_val]
  simp only [stageTwoIndirectAddress,Nat.mod_eq_of_lt lo,Nat.mod_eq_of_lt hi,
    Nat.div_eq_of_lt sum,Nat.mod_eq_of_lt sum,add_zero,if_pos hi]
  rw [cast,ZMod.natCast_zmod_val]

/-- Syntax bindings precede any witness evaluation. -/
theorem base_locations : (keyDescriptor (1 : Fin 43)).location = .indirect #v[2,3] 0 ∧
    (keyDescriptor (26 : Fin 43)).location = .indirect #v[100,101] 0 := by decide +kernel

private def locationProperty : KeyLocation → Prop
  | .register _ => True
  | .indirect base _ => base = #v[2,3] ∨ base = #v[100,101]

private instance locationDecidable (location : KeyLocation) : Decidable (locationProperty location) := by
  cases location <;> unfold locationProperty <;> infer_instance

theorem location_bases (slot : Fin 43) :
    match (keyDescriptor slot).location with
    | .register _ => True
    | .indirect base _ => base = #v[2,3] ∨ base = #v[100,101] := by
  change locationProperty (keyDescriptor slot).location
  fin_cases slot <;> decide +kernel

theorem base_bounds {w : Nat → F}
    (domains : ∀ slot : Fin 43, Airbender.NativeAddressSupport.Domain (quotientMemoryKey w slot false).address) :
    (w 2).val < 65536 ∧ (w 3).val < 65536 ∧ (w 100).val < 65536 ∧ (w 101).val < 65536 := by
  have state := domains (1 : Fin 43)
  have message := domains (26 : Fin 43)
  change Airbender.NativeAddressSupport.Domain (quotientKeyAddress w (keyDescriptor 1).location) at state
  change Airbender.NativeAddressSupport.Domain (quotientKeyAddress w (keyDescriptor 26).location) at message
  rw [base_locations.1] at state
  rw [base_locations.2] at message
  change Airbender.NativeAddressSupport.Domain ⟨0,w 2+0,w 3⟩ at state
  change Airbender.NativeAddressSupport.Domain ⟨0,w 100+0,w 101⟩ at message
  simp only [add_zero] at state message
  exact ⟨(ram_bounds state).1,(ram_bounds state).2,(ram_bounds message).1,(ram_bounds message).2⟩

theorem indirect_bounds {w : Nat → F}
    (domains : ∀ slot : Fin 43, Airbender.NativeAddressSupport.Domain (quotientMemoryKey w slot false).address) :
    IndirectBounds w := by
  have bases := base_bounds domains
  intro slot
  have source := domains slot
  have columns := Airbender.Blake2Worker.MemoryKeyProofs.location_columns slot
  have locations := location_bases slot
  cases location : (keyDescriptor slot).location with
  | register index => trivial
  | indirect base offset =>
    rw [location] at columns locations
    obtain ⟨_,_,short⟩ := columns
    have lo : (w base[0]).val < 65536 ∧ (w base[1]).val < 65536 := by
      rcases locations with rfl | rfl
      · exact ⟨bases.1,bases.2.1⟩
      · exact ⟨bases.2.2.1,bases.2.2.2⟩
    change Airbender.NativeAddressSupport.Domain (quotientKeyAddress w (keyDescriptor slot).location) at source
    rw [location] at source
    have address := ram_bounds source
    have value := sum_value lo.1 short
    rw [value] at address
    exact ⟨lo.1,lo.2,address.1⟩

theorem active_keys {w : Nat → F} (bounds : IndirectBounds w) (slot : Fin 43) (write : Bool) :
    stageTwoMemoryKey w slot write = some (quotientMemoryKey w slot write) := by
  have bound := bounds slot
  have address : stageTwoKeyAddress w (keyDescriptor slot).location = some (quotientKeyAddress w (keyDescriptor slot).location) := by
    cases location : (keyDescriptor slot).location with
    | register index => rfl
    | indirect base offset =>
      rw [location] at bound
      exact indirect_address bound.1 bound.2.1 bound.2.2
  simp only [stageTwoMemoryKey,address,Option.map_some,quotientMemoryKey]

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs batch) : Effects proofs batch inputs := by
  have addresses := Airbender.NativeAddressSupportProofs.effects embed memory ch pc gamma config accepted identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted
  have indirects : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, w constraintsABI.multiplicity = 1 → IndirectBounds w := by
    intro w member active
    exact indirect_bounds (addresses.workers w member active)
  refine ⟨addresses,indirects,?_⟩
  intro w member slot write
  have body := processing w member
  have bit := (Airbender.Blake2Worker.ProcessingProofs.effects body.conventions).multiplicityBit
  rcases bit with zero | active
  · have padding := Airbender.Blake2Worker.MemoryKeyProofs.padding_keys body
    cases write
    · exact padding.readKeys zero slot
    · exact padding.writeKeys zero slot
  · exact active_keys (indirects w member active) slot write

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,
    effects embed memory ch pc gamma config accepted.component identity⟩
end Airbender.NativeStageTwoKeyProofs

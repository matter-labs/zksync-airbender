import Airbender.Review.Circuits.ReducedMachine.CallerClockDomainTheorems
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness
import Tests.NativeInitializationBatch

namespace Airbender.Tests.NativeCallerClockDomain
open Airbender.NativeCallerClockDomain Airbender.Verification Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
abbrev F := Airbender.NativeCallerClockDomain.F
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- PURE arithmetic/domain controls; not accepted native wrap witnesses.
theorem successor_normal : 3+1=4 ∨ (3=13-1 ∧ 4=0) :=
  Airbender.NativeCallerClockDomainProofs.successor (by decide) (by decide) (by decide)

theorem successor_wrap : 12+1=0 ∨ (12=13-1 ∧ 0=0) :=
  Airbender.NativeCallerClockDomainProofs.successor (by decide) (by decide) (by decide)

theorem ordinary_domain : Domain ⟨7,0⟩ := by
  constructor <;> norm_num [mersenne31Modulus]

theorem upper_ordinary_domain : Domain ⟨1048574,524287⟩ := by
  constructor <;> norm_num [mersenne31Modulus]

theorem low_sentinel_domain : Domain ⟨mersenne31Modulus-1,0⟩ := by
  constructor <;> norm_num [mersenne31Modulus]

theorem high_sentinel_domain : Domain ⟨524287,mersenne31Modulus-1⟩ := by
  constructor <;> norm_num [mersenne31Modulus]

theorem sentinel_is_not19bit : ¬ (Airbender.Trace.Timestamp.mk (mersenne31Modulus-1) 0).Bounded ∧
    ¬ (Airbender.Trace.Timestamp.mk 524287 (mersenne31Modulus-1)).Bounded := by
  norm_num [Trace.Timestamp.Bounded,Trace.timestampBase,mersenne31Modulus]

theorem two_sentinels_rejected : ¬ Domain ⟨mersenne31Modulus-1,mersenne31Modulus-1⟩ := by
  intro domain
  have impossible := domain.lowWrap rfl
  norm_num [mersenne31Modulus] at impossible

theorem high_sentinel_below_window_rejected : ¬ Domain ⟨524286,mersenne31Modulus-1⟩ := by
  intro domain
  have impossible := (domain.highWrap rfl).1
  norm_num at impossible

theorem ordinary_low_above_window_rejected : ¬ Domain ⟨1048575,0⟩ := by
  intro domain
  have impossible := domain.low
  norm_num [mersenne31Modulus] at impossible

theorem ordinary_high_above_window_rejected : ¬ Domain ⟨0,524288⟩ := by
  intro domain
  have impossible := domain.high
  norm_num [mersenne31Modulus] at impossible

private def w (active : Bool) := Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active

theorem complete_active_body : RowEffects (w true) :=
  native_caller_clock_domain (Airbender.ReducedMachine.NativeCSRPositiveWitness.body true)

theorem complete_inactive_body : RowEffects (w false) :=
  native_caller_clock_domain (Airbender.ReducedMachine.NativeCSRPositiveWitness.body false)

theorem existing_fixture_endpoints (active : Bool) : time (w active) = ⟨7,0⟩ ∧
    (w active 15).val=8 ∧ (w active 16).val=0 := by cases active <;> decide +kernel

theorem complete_empty_domains : Effects ([] : List (Airbender.NativeInitializationBatch.Proof F)) :=
  native_all_caller_clock_domains _ _ _ _ _ _ Airbender.Tests.NativeInitializationBatch.empty_combined_component

theorem complete_conditional_domains {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) : Effects proofs :=
  native_all_caller_clock_domains embed memory ch pc gamma config accepted
end Airbender.Tests.NativeCallerClockDomain

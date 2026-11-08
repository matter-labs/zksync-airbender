import Airbender.Review.Circuits.ReducedMachine.CallerClockDomain
import Airbender.Proofs.ReducedMachine.NativeTimestamp
import Airbender.Proofs.ReducedMachine.NativeActiveWorkerClocks

namespace Airbender.NativeCallerClockDomainProofs
open Airbender.NativeCallerClockDomain Airbender.Verification Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Entire canonical successor calculation over abstract naturals. -/
theorem successor {p value result : Nat} (positive : 0 < p) (canonical : value < p)
    (equation : (value+1)%p = result) :
    value+1 = result ∨ (value = p-1 ∧ result = 0) := by
  by_cases room : value+1 < p
  · exact Or.inl (by simpa only [Nat.mod_eq_of_lt room] using equation)
  · have last : value+1 = p := by omega
    right
    rw [last,Nat.mod_self] at equation
    exact ⟨by omega,equation.symm⟩

/-- Complete finite endpoint algebra BEFORE native field/domain instantiation. -/
theorem endpoint_domain {p low high a b : Nat} (large : 1048575 < p)
    (ab : a < 524288) (bb : b < 524288)
    (alternatives : (((low+1=a ∨ (low=p-1 ∧ a=0)) ∧ high=b) ∨
      (low+1=a+524288 ∧ (high+1=b ∨ (high=p-1 ∧ b=0))))) :
    (low < 1048575 ∨ low=p-1) ∧ (high < 524288 ∨ high=p-1) ∧
      (low=p-1 → high < 524288) ∧
      (high=p-1 → 524287 ≤ low ∧ low < 1048575) := by
  rcases alternatives with ⟨normal|wrap,highEq⟩ | ⟨lowEq,normal|wrap⟩ <;> omega

theorem endpoints {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) :
    EndpointCases w := by
  obtain ⟨carry,bit,low,high⟩ := Airbender.ReducedMachine.NativeClockProofs.timestamp_equations holds
  have bounds := Airbender.ReducedMachine.NativeClockProofs.final_clock_bound holds
  change (w 15).val < 524288 ∧ (w 16).val < 524288 at bounds
  have positive : 0 < mersenne31Modulus := by decide
  have shifted : (w 2+3)+1 = w 15+524288*carry := by linear_combination low
  have lowField : (((w 2+3).val+1 : Nat) : F) = ((w 15).val+524288*carry : Nat) := by
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val] using shifted
  have rhs : (w 15).val+524288*carry < mersenne31Modulus := by
    change (w 15).val+524288*carry < 2147483647
    nlinarith [bounds.1]
  have lowMod : ((w 2+3).val+1)%mersenne31Modulus = (w 15).val+524288*carry := by
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt rhs] using congrArg ZMod.val lowField
  have lowCases := successor positive (ZMod.val_lt (w 2+3)) lowMod
  rcases (show carry=0 ∨ carry=1 by omega) with rfl | rfl
  · have highEq : w 3 = w 16 := by simpa using high
    left
    constructor
    · simpa [time,Trace.timeOfPair] using lowCases
    · change (w 3).val = (w 16).val
      exact congrArg ZMod.val highEq
  · have highField : (((w 3).val+1 : Nat) : F) = (w 16).val := by
      simpa only [Nat.cast_add,Nat.cast_one,ZMod.natCast_zmod_val] using high
    have highMod : ((w 3).val+1)%mersenne31Modulus = (w 16).val := by
      have upper : (w 16).val < mersenne31Modulus := ZMod.val_lt _
      simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt upper] using congrArg ZMod.val highField
    have highCases := successor positive (ZMod.val_lt (w 3)) highMod
    have noLowWrap : ¬ ((w 2+3).val = mersenne31Modulus-1 ∧ (w 15).val+524288*1=0) := by omega
    right
    exact ⟨by simpa [time,Trace.timeOfPair] using lowCases.resolve_right noLowWrap,
      by simpa [time,Trace.timeOfPair] using highCases⟩

theorem body {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : RowEffects w := by
  have bounds := Airbender.ReducedMachine.NativeClockProofs.final_clock_bound holds
  change (w 15).val < 524288 ∧ (w 16).val < 524288 at bounds
  have alternatives := endpoints holds
  have domain := endpoint_domain (p := mersenne31Modulus) (by decide) bounds.1 bounds.2 alternatives
  exact ⟨bounds,alternatives,⟨domain.1,domain.2.1,domain.2.2.1,domain.2.2.2⟩⟩

theorem all_rows {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) : Effects proofs := by
  have source : ∀ proof ∈ Airbender.NativeInitializationBatch.mainProofs proofs, ∀ i < callerAuxiliaryLayout.traceLength-1,
      RowEffects (proof.rows i) := by
    intro proof member i bound
    obtain ⟨origin,present,rfl⟩ := List.mem_map.mp member
    exact body ((accepted.arguments.mainDelegation origin.main (List.mem_map.mpr ⟨origin,present,rfl⟩)).body i bound)
  exact Airbender.NativeActiveWorkerClockProofs.sampled_property
    (Airbender.NativeInitializationBatch.mainProofs proofs) (fun proof => proof.rows)
    (callerAuxiliaryLayout.traceLength-1) RowEffects source
end Airbender.NativeCallerClockDomainProofs

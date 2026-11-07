import Airbender.Review.Circuits.ReducedMachine.InitializationRangeTheorems
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness

namespace Airbender.Tests.NativeInitializationRange
open Airbender.NativeInitializationRange Airbender.NativeInitializationRangeProofs
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
private abbrev csr := Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment
private abbrev identity := RingHom.id F
private theorem csr_address (active : Bool) : Airbender.NativeInitializationOrdering.address (csr active) = #v[0,0] := by
  cases active <;> decide +kernel

theorem actual_geometry : initializationRangeLayout.product.index = 4 ∧
    initializationRangeLayout.accumulator.start = 28 ∧
    importedConstraintsArgumentColumns.initialAddress = #v[126,127] :=
  ⟨geometry.2.2.2.2.1,geometry.2.2.2.2.2.1,geometry.2.2.2.2.2.2⟩

theorem both_product_scalings : productTerm (2 : F) 3 5 30 = 0 ∧
    productTerm (2 : F) 3 5 15 = 30 := by decide +kernel

theorem rational_scaling : rationalTerm (2 : F) 7 3 5 30 11 = 4832 := by decide +kernel

/-- Complete existing native BODY plus the individual extra address-pair slice.
    No full auxiliary/global/worker/physical accepted witness is claimed. -/
theorem complete_body_pair (active : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (csr active)) (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) ∧
      PairAccepted identity 1 (csr active) (fun _ => 0) (fun _ => 2) := by
  refine ⟨Airbender.ReducedMachine.NativeCSRPositiveWitness.body active,?_⟩
  cases active <;> exact ⟨by decide +kernel,by decide +kernel⟩

theorem base_four_not_execute : csr true 4 = 1 ∧
    PairAccepted identity 1 (csr true) (fun _ => 0) (fun _ => 2) :=
  ⟨by decide +kernel,(complete_body_pair true).2⟩

/-- Complete BODY at the double pole admits arbitrary extra pair accumulator.
    This is local; native scalar-family sums/multiplicities are separate. -/
theorem complete_body_double_pole (active : Bool) (value : F) :
    PairAccepted identity 0 (csr active) (fun _ => 0) (fun _ => value) := by
  constructor <;> simp [productTerm,rationalTerm,csr_address,identity]

private theorem pair_of_addresses (w : Nat → F) (a b gamma c value : F)
    (observed : Airbender.NativeInitializationOrdering.address w = #v[a,b])
    (p : productTerm (1 : F) a b c = 0) (q : rationalTerm (1 : F) gamma a b c value = 0) :
    PairAccepted identity gamma w (fun _ => c) (fun _ => value) := by
  constructor
  · simpa [observed] using p
  · simpa [observed,identity] using q

private def wide (column : Nat) : F := if column = 126 ∨ column = 127 then 70000 else 0

/-- PURE wide-address double-pole SLICE, not accepted complete native body or
    global proof. It prevents claiming address ranges from these equations. -/
theorem wide_pair_slice (value : F) :
    PairAccepted identity (-70000) wide (fun _ => (70000 : F)*70000) (fun _ => value) ∧
      (Airbender.NativeInitializationOrdering.address wide)[0].val ≥ 65536 := by
  refine ⟨pair_of_addresses wide 70000 70000 (-70000) (70000*70000) value
    (by decide +kernel) (double_pole (70000 : F) value).1 (double_pole (70000 : F) value).2,?_⟩
  decide +kernel

theorem bad_product_rejected : productTerm (1 : F) 3 5 14 ≠ 0 := by decide +kernel

theorem single_pole_rejected (value : F) : rationalTerm (1 : F) (-3) 3 5 15 value ≠ 0 := by
  simp only [rationalTerm,one_mul,mul_one]
  have e : ((-3 : F)^2+(-3)*(3+5)+15) = 0 := by decide +kernel
  rw [e,zero_mul]
  decide +kernel

theorem duplicate_nonpole_not_free : rationalTerm (1 : F) 1 0 0 0 17 ≠ 0 := by decide +kernel

theorem actual_all_ordinary_rows : initializationRangeLayout.traceLength-1 = 8388607 ∧
    initializationRangeLayout.traceLength-2 = 8388606 := by decide +kernel

theorem complete_conditional_pair {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof) :
    ∀ i < initializationRangeLayout.traceLength-1,
      (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[0])*
        (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[1])*
        proof.main.auxiliary i initializationRangeLayout.accumulator =
      (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[0])+
        (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[1]) :=
  native_initialization_address_pairs embed memory pc gamma accepted
end Airbender.Tests.NativeInitializationRange

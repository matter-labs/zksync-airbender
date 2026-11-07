import Airbender.Review.Circuits.ReducedMachine.InitializationOrdering
import Airbender.Proofs.ReducedMachine.NativeMainAuxiliary
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Proofs.ReducedMachine.NativeMemoryTokens

namespace Airbender.NativeInitializationOrderingProofs
open NativeInitializationOrdering Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem geometry : importedConstraintsArgumentColumns.initialAddress = #v[126,127] ∧
    importedConstraintsArgumentColumns.addressAux = #v[122,123] ∧
    importedConstraintsArgumentColumns.addressBorrows = #v[124,125] ∧
    callerAuxiliaryLayout.traceLength-2 = 8388606 := by decide +kernel

/-- Entire actual-body calculation over an ABSTRACT setup table before concrete
    RuntimePool instantiation. Address limb bounds are not among the conclusions. -/
theorem body_controls {setup : Table F (fields 4)} {w : Nat → F}
    (body : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (remainder w)[0].val < 65536 ∧ (remainder w)[1].val < 65536 ∧
      ((borrows w)[0] = 0 ∨ (borrows w)[0] = 1) ∧ ((borrows w)[1] = 0 ∨ (borrows w)[1] = 1) := by
  have low := Verification.range16_bound (Verification.lookup_of_holds body ⟨6,by change 6 < 22; decide⟩)
  have high := Verification.range16_bound (Verification.lookup_of_holds body ⟨7,by change 7 < 22; decide⟩)
  have bitLow := Verification.assertion_of_holds body ⟨25,by change 25 < 117; decide⟩
  have bitHigh := Verification.assertion_of_holds body ⟨26,by change 26 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,Verification.environment] at bitLow bitHigh
  have lowBit : w 124*(w 124-1) = 0 := by linear_combination bitLow
  have highBit : w 125*(w 125-1) = 0 := by linear_combination bitHigh
  refine ⟨?_,?_,?_,?_⟩
  · simpa [remainder,geometry.2.1,Arithmetic.limbBase,Expression.eval,Verification.environment] using low
  · simpa [remainder,geometry.2.1,Arithmetic.limbBase,Expression.eval,Verification.environment] using high
  · simpa [borrows,geometry.2.2.1] using (mul_eq_zero.mp lowBit).imp id sub_eq_zero.mp
  · simpa [borrows,geometry.2.2.1] using (mul_eq_zero.mp highBit).imp id sub_eq_zero.mp

private theorem zero_borrow {aux borrow : F} (bound : aux.val < 65536)
    (bit : borrow = 0 ∨ borrow = 1) (equation : 65536*borrow = aux) : borrow = 0 ∧ aux = 0 := by
  rcases bit with zero | one
  · simp_all
  · have value : aux.val = 65536 := by rw [← equation,one]; decide +kernel
    omega

/-- Equal RAW field addresses cancel directly. This needs no address range,
    radix-packing injectivity or expected comparison bit. -/
theorem repeated_controls {w next : Nat → F}
    (ranges : (remainder w)[0].val < 65536 ∧ (remainder w)[1].val < 65536)
    (bits : ((borrows w)[0] = 0 ∨ (borrows w)[0] = 1) ∧ ((borrows w)[1] = 0 ∨ (borrows w)[1] = 1))
    (accepted : AdjacentAccepted w next) (same : address w = address next) :
    borrows w = #v[0,0] ∧ remainder w = #v[0,0] := by
  have low := accepted.low
  have high := accepted.high
  rw [same] at low high
  simp only [lowTerm,highTerm,one_mul] at low high
  have lowEquation : 65536*(borrows w)[0] = (remainder w)[0] := by linear_combination low
  obtain ⟨borrowLow,auxLow⟩ := zero_borrow ranges.1 bits.1 lowEquation
  have highEquation : 65536*(borrows w)[1] = (remainder w)[1] := by linear_combination high+borrowLow
  obtain ⟨borrowHigh,auxHigh⟩ := zero_borrow ranges.2 bits.2 highEquation
  constructor
  · apply Vector.ext
    intro i bound
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact borrowLow
    · exact borrowHigh
  · apply Vector.ext
    intro i bound
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact auxLow
    · exact auxHigh

theorem repeated_padding {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {w next : Nat → F} {aux : Airbender.Blake2Worker.QuarticColumn → R} {nextGrand : R}
    (main : RowAccepted embed memory pc w aux nextGrand)
    (adjacent : AdjacentAccepted w next) (same : address w = address next) :
    PaddingRecord w ∧ borrows w = #v[0,0] ∧ remainder w = #v[0,0] := by
  obtain ⟨low,high,bitLow,bitHigh⟩ := body_controls main.body
  obtain ⟨zero,auxZero⟩ := repeated_controls ⟨low,high⟩ ⟨bitLow,bitHigh⟩ adjacent same
  refine ⟨Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_padding embed memory pc main ?_,zero,auxZero⟩
  have highZero := congrArg (fun value : Vector F 2 => value[1]) zero
  simpa [borrows] using highZero

theorem token_address_binding {w next : Nat → F}
    (same : (Airbender.NativeMemoryTokens.encodeKey (initializationKey w true)).address =
      (Airbender.NativeMemoryTokens.encodeKey (initializationKey next true)).address) : address w = address next := by
  have raw := Airbender.NativeMemoryTokenProofs.address_injective same
  have limbs := congrArg (fun key : MemoryKeyAddress => #v[key.low,key.high]) raw
  simpa [initializationKey,address,geometry.1] using limbs

theorem full_domain_repeats {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) {proof : MainProof R}
    (accepted : NativeInitializationOrdering.Accepted embed memory pc proof) :
    ∀ i < callerAuxiliaryLayout.traceLength-2, address (proof.rows i) = address (proof.rows (i+1)) →
      PaddingRecord (proof.rows i) ∧ borrows (proof.rows i) = #v[0,0] ∧ remainder (proof.rows i) = #v[0,0] := by
  intro i bound same
  exact repeated_padding embed memory pc (accepted.main.rows i (by omega)) (accepted.adjacent i bound) same

end Airbender.NativeInitializationOrderingProofs

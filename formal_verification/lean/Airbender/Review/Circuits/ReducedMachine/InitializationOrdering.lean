import Airbender.Review.Circuits.ReducedMachine.MainAuxiliary

namespace Airbender.NativeInitializationOrdering
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
abbrev F := ZMod mersenne31Modulus

def address (w : Nat → F) : Vector F 2 := importedConstraintsArgumentColumns.initialAddress.map w

def remainder (w : Nat → F) : Vector F 2 := importedConstraintsArgumentColumns.addressAux.map w

def borrows (w : Nat → F) : Vector F 2 := importedConstraintsArgumentColumns.addressBorrows.map w

/-- Actual native adjacent low/high linear polynomials. Each has ONE outer
    half-domain scaling; no desired subtraction/comparison result is supplied. -/
def lowTerm {R : Type} [CommRing R] (tau current next aux borrow : R) : R :=
  tau*(65536*borrow+current-next-aux)

def highTerm {R : Type} [CommRing R] (tau current next aux lowBorrow highBorrow : R) : R :=
  tau*(65536*highBorrow+current-lowBorrow-next-aux)

/-- Individual unit-normalized source-reference ordering relations, separate
    from physical quotient/LDE extraction. Raw address limbs are NOT assumed
    16-bit. Original complete body derives remainder ranges and borrow bits. -/
structure AdjacentAccepted (w next : Nat → F) : Prop where
  low : lowTerm (1 : F) (address w)[0] (address next)[0] (remainder w)[0] (borrows w)[0] = 0
  high : highTerm (1 : F) (address w)[1] (address next)[1] (remainder w)[1] (borrows w)[0] (borrows w)[1] = 0

/-- Actual ordinary domain: compare every row EXCEPT the last TWO physical
    rows. Complete existing main acceptance, all init padding and both grand
    boundaries remain on the SAME proof. No address bounds/order/public seed,
    first/one-before-last init answer or global setup equivalence is supplied. -/
structure Accepted {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R) (proof : MainProof R) : Prop where
  main : Airbender.ReducedMachine.NativeMainAuxiliary.Accepted embed memory pc proof
  adjacent : ∀ i < callerAuxiliaryLayout.traceLength-2, AdjacentAccepted (proof.rows i) (proof.rows (i+1))

def PaddingRecord (w : Nat → F) : Prop := ∀ column ∈ initializationColumns, w column = 0

end Airbender.NativeInitializationOrdering

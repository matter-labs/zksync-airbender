import Airbender.Review.Circuits.Blake2Worker.ProcessingArtifact
import Airbender.Review.Circuits.Blake2Worker.Memory

namespace Airbender.Blake2Worker.Native
open Verification ProcessingArtifact

/-- Reviewed source reference: every_row_except_last.rs processing conventions.
    The native half-domain scaling stays explicit, including both mask factors. -/
def processingBitTerm {R : Type} [CommRing R] (tau multiplicity : R) : R :=
  (tau*multiplicity)*(tau*multiplicity-1)

def processingMaskTerm {R : Type} [CommRing R] (tau multiplicity value : R) : R :=
  (tau*multiplicity-1)*tau*value

def processingBitExpression {p : Nat} : Expression (ZMod p) :=
  .mul (.var ⟨processingMultiplicity⟩) (.add (.var ⟨processingMultiplicity⟩) (.const (-1)))

def processingMaskExpression {p : Nat} (column : Nat) : Expression (ZMod p) :=
  .mul (.add (.var ⟨processingMultiplicity⟩) (.const (-1))) (.var ⟨column⟩)

/-- Individual native processing-convention polynomials at unit normalization.
    This is separate from the352 JSON equations and from physical quotient,
    challenge separation, LDE and last-row enforcement. -/
def processingConstraints {p : Nat} : List (FlatOperation (ZMod p)) :=
  [.assert processingBitExpression] ++ processingMaskedColumns.toList.map
    (fun column => .assert (processingMaskExpression column))

/-- Explicit logical interface for ordinary worker rows: complete native body
    and the individual normalized native processing conventions. No active flag,
    zero-clock exclusion, issued stream or desired worker result is supplied. -/
structure LocalProcessingAccepted (w : Nat → ZMod mersenne31Modulus) : Prop where
  body : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table)
  conventions : FlatOperation.ConstraintsHoldFlat (environment w) processingConstraints

structure ProcessingEffects (w : Nat → ZMod mersenne31Modulus) : Prop where
  multiplicityBit : w constraintsABI.multiplicity = 0 ∨ w constraintsABI.multiplicity = 1
  paddingMemory : w constraintsABI.multiplicity = 0 →
    ∀ column ∈ processingMemoryColumns.toList, w column = 0
  paddingAccesses : w constraintsABI.multiplicity = 0 → ∀ slot : Fin 43,
    w (memoryAccess slot).readTime[0] = 0 ∧ w (memoryAccess slot).readTime[1] = 0 ∧
    w (memoryAccess slot).readValue[0] = 0 ∧ w (memoryAccess slot).readValue[1] = 0 ∧
    w ((memoryAccess slot).writeValue.getD (memoryAccess slot).readValue)[0] = 0 ∧
    w ((memoryAccess slot).writeValue.getD (memoryAccess slot).readValue)[1] = 0

end Airbender.Blake2Worker.Native

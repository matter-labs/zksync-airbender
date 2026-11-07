import Airbender.Review.Circuits.Blake2Worker.Queries

namespace Airbender.Blake2Worker.Native
open Verification

/-- Native descriptor order retains all43 old reads, both readonly register
    refreshes and all25 written accesses. No memory matching is asserted here. -/
def memoryAccesses : Array Access :=
  constraintsABI.registers.flatMap fun register => #[register.access] ++ register.indirects

def memoryAccess (slot : Fin 43) : Access := memoryAccesses[slot.val]!

def clockBorrowColumn (slot : Fin 43) : Nat := constraintsABI.booleanColumns[125+slot.val]!

def lowClockDifference (w : Nat → ZMod mersenne31Modulus) (slot : Fin 43) : ZMod mersenne31Modulus :=
  w (memoryAccess slot).readTime[0] - w constraintsABI.writeTime[0] + 524288*w (clockBorrowColumn slot)

def highClockDifference (w : Nat → ZMod mersenne31Modulus) (slot : Fin 43) : ZMod mersenne31Modulus :=
  524288*w constraintsABI.multiplicity + w (memoryAccess slot).readTime[1] -
    w constraintsABI.writeTime[1] - w (clockBorrowColumn slot)

/-- Derived canonical alignment is weaker than initialized16bit read bounds.
    Difference bounds are not raw timestamp bounds or chronological matching. -/
structure LocalMemoryEffects (w : Nat → ZMod mersenne31Modulus) : Prop where
  stateQuotient : (w 2).val = 128*(16777216*w 2).val
  stateAligned : (w 2).val % 128 = 0
  stateBound : (w 2).val < 8388608
  messageQuotient : (w 100).val = 64*(33554432*w 100).val
  messageAligned : (w 100).val % 64 = 0
  messageBound : (w 100).val < 4194304
  borrowBits : ∀ slot : Fin 43, w (clockBorrowColumn slot) = 0 ∨ w (clockBorrowColumn slot) = 1
  lowDifferences : ∀ slot : Fin 43, (lowClockDifference w slot).val < 524288
  highDifferences : ∀ slot : Fin 43, (highClockDifference w slot).val < 524288

end Airbender.Blake2Worker.Native

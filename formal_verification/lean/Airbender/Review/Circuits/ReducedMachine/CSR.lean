import Airbender.Review.Circuits.ReducedMachine.ArithmeticResult
import Airbender.Review.Circuits.ReducedMachine.Tables.CSR

namespace Airbender.ReducedMachine.Native
open Arithmetic
set_option autoImplicit false
/-- Selected actual native CSRRW mask; original public decoding is separate. -/
def csrMask : Nat := 129

def csrOracleWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 90).val,(w 91).val⟩
def csrCandidate (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 2 := #v[w 116,w 117]

/-- Read imported native request coordinates, retaining an absent ABI group as
    absent. This observer does not assert issuance, fulfillment or accounting. -/
structure CSRRequest where
  multiplicity : ZMod mersenne31Modulus
  kind : ZMod mersenne31Modulus
  offsetHigh : Option (ZMod mersenne31Modulus)
  clockOffset : Nat
  deriving DecidableEq

def csrRequest (w : Nat → ZMod mersenne31Modulus) : CSRRequest :=
  ⟨w importedConstraintsRequestColumns.multiplicity,w importedConstraintsRequestColumns.kind,
    importedConstraintsRequestColumns.offsetHigh.map w,importedConstraintsRequestColumns.clockOffset⟩

/-- Actual local native CSR observables under the exact explicit fixture.
    No original CSR read, custom-operation success or worker effect is asserted. -/
structure CSRNativeEffects (w : Nat → ZMod mersenne31Modulus) : Prop where
  key : (w 9).val = 1984 ∨ (w 9).val = 1988 ∨ (w 9).val = 1989
  supported : w 64 = 1
  delegated : w 65 = (NativeFixed.csrDelegated (w 9).val : Nat)
  selected : source2 w = #v[w 9,w 10]
  secondPort : w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1
  tags : lookupSelectors w = #v[25,0,0,0]
  candidate : csrCandidate w = #v[w 90,w 91]
  destination : rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0)
  written : rdWrite w = (csrCandidate w).map (fun value => (1-rdZeroFlag w)*value)
  oracleBounded : (csrOracleWord w).Bounded
  delegationZero : NativeFixed.csrDelegated (w 9).val = 1 → csrOracleWord w = ⟨0,0⟩
  request : csrRequest w =
    ⟨(NativeFixed.csrDelegated (w 9).val : Nat),w 9*(NativeFixed.csrDelegated (w 9).val : Nat),
      some (w 36*(NativeFixed.csrDelegated (w 9).val : Nat)),3⟩
  offsetBounded : (w 93).val < 65536
  pc : #v[w 13,w 14] = #v[w 49,w 50]
end Airbender.ReducedMachine.Native

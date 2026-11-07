import Airbender.Review.Circuits.ReducedMachine.ArithmeticResult
import Airbender.Review.Circuits.ReducedMachine.ShiftOperand

namespace Airbender.ReducedMachine.Native
open Arithmetic
set_option autoImplicit false

/-- Native custom Mersenne31 arithmetic, separate from upstream Zimop's fallback.
    Original decoding/reference execution and physical enforcement are separate. -/
inductive MOPMode
  | add | sub | mul
  deriving DecidableEq

def MOPMode.mask : MOPMode → Nat
  | .add => 34819 | .sub => 133123 | .mul => 67587

def MOPMode.useRegister (_ : MOPMode) : Bool := true

/-- Pure field operation, with no architectural state or desired row value. -/
def MOPMode.field : MOPMode → ZMod mersenne31Modulus → ZMod mersenne31Modulus → ZMod mersenne31Modulus
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·)

def mopOutputWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 61).val,(w 62).val⟩
def mopCandidate (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 2 := #v[w 116,w 117]

/-- Actual local native MOP observables. Source words are native port values,
    not yet original pre-state Sail reads or a complete fetched execution. -/
structure MOPNativeEffects (w : Nat → ZMod mersenne31Modulus) (mode : MOPMode) : Prop where
  source : source2 w = #v[w 37,w 38]
  secondPort : w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1
  tags : lookupSelectors w = #v[0,0,0,0]
  candidate : mopCandidate w = #v[w 61,w 62]
  destination : rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0)
  written : rdWrite w = (mopCandidate w).map (fun value => (1-rdZeroFlag w)*value)
  bounded : (mopOutputWord w).Bounded
  canonical : (mopOutputWord w).value < mersenne31Modulus
  result : (mopOutputWord w).value =
    (mode.field ((sourceWord w).value : ZMod mersenne31Modulus) ((registerOperandWord w).value : ZMod mersenne31Modulus)).val
  pc : #v[w 13,w 14] = #v[w 49,w 50]

end Airbender.ReducedMachine.Native

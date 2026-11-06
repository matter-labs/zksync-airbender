import Airbender.Review.Circuits.ReducedMachine.ArithmeticResult
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control

namespace Airbender.ReducedMachine.Native
open Arithmetic Verification

/-- Actual reduced update-rd/CONDITIONAL_COMMON_KEY masks for comparisons.
    Branch forms and original public decoding remain separate. -/
def comparisonMask (useRegister : Bool) : Nat := 65 + if useRegister then 2 else 0

/-- Actual monolithic resolver packs funct3 and four flags into one key, and
    returns separate jump/comparison columns. It differs from split tag43. -/
def conditionalFlag (bits funct3 : Nat) : Bool :=
  let unsigned := bits % 2 == 1
  let equal := bits / 2 % 2 == 1
  let different := (bits / 4 % 2 == 1) != (bits / 8 % 2 == 1)
  let signed := if different then !unsigned else unsigned
  match funct3 with
  | 0 => equal | 1 => !equal | 2 => signed | 3 => unsigned
  | 4 => signed | 5 => !signed | 6 => unsigned | _ => !unsigned

def conditionalRow (i : Fin 128) : Vector Nat 4 :=
  let comparison := i.val % 8 == 2 || i.val % 8 == 3
  let result := if conditionalFlag (i.val / 8) (i.val % 8) then 1 else 0
  #v[i.val,if comparison then 0 else result,if comparison then result else 0,22]

/-- Actual local routing, Boolean comparison output, PC and masked-port effects.
    Original decoder rd/x0 and initialized Sail execution remain separate. -/
def ComparisonEffects (w : Nat → ZMod mersenne31Modulus) (useRegister : Bool) : Prop :=
  source2 w = (if useRegister then #v[w 37,w 38] else #v[w 9,w 10]) ∧
  (w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1) ∧ w 66 = 0 ∧
  (w 67 = 0 ∨ w 67 = 1) ∧ (candidateWord w).Bounded ∧
  finalPC w = defaultPC w ∧
  rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0) ∧
  rdWrite w = (arithmeticCandidate w).map (fun value => (1-rdZeroFlag w)*value)

end Airbender.ReducedMachine.Native

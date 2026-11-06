import Slop.KeccakSplit.Chi5.Queries

/- Each 16-bit memory limb of a chi5 lane is its four queried nibbles: three are
   witness columns, the top one is the limb minus them over 4096 (field inverse). -/

namespace Airbender.Keccak.Split.Chi5.Proofs
open Airbender.Trace Airbender.Keccak.Split.Proofs
set_option warningAsError true

/-- Column of limb `limb` of lane `lane`, read or written (ports 2 + 2·lane, 3 + 2·lane). -/
def limbColumn (writing : Bool) (lane : Fin 5) (limb : Fin 4) : Nat :=
  14 + 8 * lane.val + (if writing then 2 else 0) + limb.val % 2 + 4 * (limb.val / 2)

def limbOf (w : Nat → ZMod babyBearModulus) (writing : Bool) (lane : Fin 5) (limb : Fin 4) :
    ZMod babyBearModulus :=
  w (limbColumn writing lane limb)

/-- Nibble `digit` of lane `lane` in its chi query, read or written. -/
noncomputable def nibble (w : Nat → ZMod babyBearModulus) (writing : Bool) (lane : Fin 5)
    (digit : Fin 16) : ZMod babyBearModulus :=
  (nibbleRow w digit)[if writing then 5 + lane.val else lane.val]'(by
    have := lane.isLt; split <;> omega)

theorem pack_eq {L a b c n : ZMod babyBearModulus}
    (hn : n = -491520 * L + 491520 * a + 7864320 * b + 125829120 * c) :
    L = a + 16 * b + 256 * c + 4096 * n := by
  have char : (2013265921 : ZMod babyBearModulus) = 0 := by decide
  subst hn
  linear_combination (L - a - 16 * b - 256 * c) * char

theorem packing (w : Nat → ZMod babyBearModulus) (writing : Bool) (lane : Fin 5) (limb : Fin 4) :
    limbOf w writing lane limb =
      nibble w writing lane ⟨4 * limb.val, by omega⟩ +
        16 * nibble w writing lane ⟨4 * limb.val + 1, by omega⟩ +
        256 * nibble w writing lane ⟨4 * limb.val + 2, by omega⟩ +
        4096 * nibble w writing lane ⟨4 * limb.val + 3, by omega⟩ := by
  apply pack_eq
  cases writing <;> fin_cases lane <;> fin_cases limb <;>
    simp only [limbOf, limbColumn, nibble, nibbleRow, Bool.false_eq_true, ↓reduceIte] <;>
    (repeat rw [getElem_cast_map]) <;> simp only [nibbleQuery] <;> op_index <;>
    simp [Expression.eval, Verification.environment]

end Airbender.Keccak.Split.Chi5.Proofs

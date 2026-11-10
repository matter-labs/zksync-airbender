module
public import Slop.KeccakSplit.ThetaRho.Queries
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

/- Theta/rho lane limbs and the bytes of its queries (ported from PR #585's
   SplitThetaBytes). -/

namespace Airbender.Keccak.Split.ThetaRho.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

/-- Value columns (low limb) of port `k`, read and written: x10, x11, lanes 0–4,
    then the readonly parities C[x-1] (lane 5) and C[x+1] (lane 6). -/
def readCol (k : Nat) : Nat :=
  if k = 0 then 3 else if k = 1 then 14 else if k < 12 then 16 + 4 * (k - 2) else 56 + 2 * (k - 12)

def writeCol (k : Nat) : Nat :=
  if k = 0 then 5 else if k = 1 then 14 else if k < 12 then 18 + 4 * (k - 2) else 56 + 2 * (k - 12)

def limbColumn (writing : Bool) (lane : Fin 7) (limb : Fin 4) : Nat :=
  (if writing then writeCol else readCol) (2 + 2 * lane.val + limb.val / 2) + limb.val % 2

def limbOf (w : Nat → ZMod babyBearModulus) (writing : Bool) (lane : Fin 7) (limb : Fin 4) :
    ZMod babyBearModulus :=
  w (limbColumn writing lane limb)

/-- Byte `digit` of state lane `lane` in its XOR-and-split query. -/
noncomputable def stateByte (w : Nat → ZMod babyBearModulus) (lane : Fin 5) (digit : Fin 8) :
    ZMod babyBearModulus :=
  (row w ⟨10 + 8 * lane.val + digit.val, by omega⟩)[0]

/-- Byte `digit` of C[x-1], of C[x+1] rotated by one, and of D, in the D-byte query. -/
noncomputable def previousByte (w : Nat → ZMod babyBearModulus) (digit : Fin 8) : ZMod babyBearModulus :=
  (row w ⟨1 + digit.val, by omega⟩)[0]

noncomputable def rotatedByte (w : Nat → ZMod babyBearModulus) (digit : Fin 8) : ZMod babyBearModulus :=
  (row w ⟨1 + digit.val, by omega⟩)[1]

noncomputable def dByte (w : Nat → ZMod babyBearModulus) (digit : Fin 8) : ZMod babyBearModulus :=
  (row w ⟨1 + digit.val, by omega⟩)[2]

/-- The low or high fragment of a state byte XOR D, rotated by the lane's shift. -/
noncomputable def fragmentByte (w : Nat → ZMod babyBearModulus) (high : Bool) (lane : Fin 5)
    (digit : Fin 8) : ZMod babyBearModulus :=
  (row w ⟨10 + 8 * lane.val + digit.val, by omega⟩)[if high then 4 else 3]'(by split <;> decide)

/-- The shift of state lane `lane` (shared by its eight split queries). -/
noncomputable def rotationShift (w : Nat → ZMod babyBearModulus) (lane : Fin 5) : ZMod babyBearModulus :=
  (row w ⟨10 + 8 * lane.val, by omega⟩)[2]

theorem state_byte_bound {w : Nat → ZMod babyBearModulus} (h : Holds w) (lane : Fin 5) (digit : Fin 8) :
    (stateByte w lane digit).val < 256 := by
  have facts := split_facts h ⟨8 * lane.val + digit.val, by omega⟩
  simpa only [stateByte, Nat.add_assoc] using facts.1

theorem d_operand_bounds {w : Nat → ZMod babyBearModulus} (h : Holds w) (digit : Fin 8) :
    (previousByte w digit).val < 256 ∧ (rotatedByte w digit).val < 256 ∧ (dByte w digit).val < 256 :=
  let facts := xor_facts h digit
  ⟨facts.1, facts.2.1, facts.2.2.1⟩

theorem d_byte_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (digit : Fin 8) :
    (dByte w digit).val = (previousByte w digit).val ^^^ (rotatedByte w digit).val :=
  (xor_facts h digit).2.2.2

theorem d_query_shared (w : Nat → ZMod babyBearModulus) (lane : Fin 5) (digit : Fin 8) :
    (row w ⟨10 + 8 * lane.val + digit.val, by omega⟩)[1] = dByte w digit := by
  simp only [dByte, row_entry, query]
  fin_cases lane <;> fin_cases digit <;> (op_index) <;> simp [Expression.eval, Verification.environment]

theorem shift_query_shared (w : Nat → ZMod babyBearModulus) (lane : Fin 5) (digit : Fin 8) :
    (row w ⟨10 + 8 * lane.val + digit.val, by omega⟩)[2] = rotationShift w lane := by
  simp only [rotationShift, row_entry, query]
  fin_cases lane <;> fin_cases digit <;> (op_index) <;> simp [Expression.eval, Verification.environment]

theorem fragment_byte_bound {w : Nat → ZMod babyBearModulus} (h : Holds w) (high : Bool)
    (lane : Fin 5) (digit : Fin 8) : (fragmentByte w high lane digit).val < 256 := by
  have facts := split_facts h ⟨8 * lane.val + digit.val, by omega⟩
  cases high
  · simpa only [fragmentByte, Nat.add_assoc, Bool.false_eq_true, ↓reduceIte] using facts.2.2.2.1
  · simpa only [fragmentByte, Nat.add_assoc, ↓reduceIte] using facts.2.2.2.2.1

theorem fragment_byte_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (lane : Fin 5)
    (digit : Fin 8) :
    (fragmentByte w false lane digit).val =
      ((stateByte w lane digit).val ^^^ (dByte w digit).val) * 2 ^ (rotationShift w lane).val % 256 ∧
      (fragmentByte w true lane digit).val =
        ((stateByte w lane digit).val ^^^ (dByte w digit).val) / 2 ^ (8 - (rotationShift w lane).val) := by
  have facts := split_facts h ⟨8 * lane.val + digit.val, by omega⟩
  have low := facts.2.2.2.2.2.1
  have high := facts.2.2.2.2.2.2
  have sharedD := d_query_shared w lane digit
  have sharedShift := shift_query_shared w lane digit
  simp only [Nat.add_assoc] at sharedD sharedShift
  rw [sharedD, sharedShift] at low high
  simpa only [fragmentByte, stateByte, Nat.add_assoc, Bool.false_eq_true, ↓reduceIte] using
    And.intro low high

/-- The parity lanes 5 and 6 are readonly. -/
theorem readonly_limb (w : Nat → ZMod babyBearModulus) (lane : Fin 2) (limb : Fin 4) :
    limbOf w true ⟨5 + lane.val, by omega⟩ limb = limbOf w false ⟨5 + lane.val, by omega⟩ limb := by
  fin_cases lane <;> fin_cases limb <;> rfl

end Airbender.Keccak.Split.ThetaRho.Proofs

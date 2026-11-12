module
public import Slop.KeccakSplit.ColumnParity.Queries
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

/- Column-parity lane limbs and the five-input XOR of the written lanes (ported from
   PR #585's SplitParityPacking, SplitParityLimbOperation, SplitParityLaneOperation). -/

namespace Airbender.Keccak.Split.ColumnParity.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

/-- Value columns (low limb) of port `k`, read and written: x10, x11, lane 0
    (written), lanes 1–4 (readonly), lane 5 (written). -/
def readCol (k : Nat) : Nat :=
  if k = 0 then 3 else if k = 1 then 13 else if k < 4 then 15 + 4 * (k - 2)
  else if k < 12 then 23 + 2 * (k - 4) else 39 + 4 * (k - 12)

def writeCol (k : Nat) : Nat :=
  if k = 0 then 5 else if k = 1 then 13 else if k < 4 then 17 + 4 * (k - 2)
  else if k < 12 then 23 + 2 * (k - 4) else 41 + 4 * (k - 12)

/-- Column of limb `limb` of lane `lane` (ports 2 + 2·lane, 3 + 2·lane). -/
def limbColumn (writing : Bool) (lane : Fin 6) (limb : Fin 4) : Nat :=
  (if writing then writeCol else readCol) (2 + 2 * lane.val + limb.val / 2) + limb.val % 2

def limbOf (w : Nat → ZMod babyBearModulus) (writing : Bool) (lane : Fin 6) (limb : Fin 4) :
    ZMod babyBearModulus :=
  w (limbColumn writing lane limb)

/-- Nibble `digit` of written lane `operand` (5: the parity) in its XOR query. -/
noncomputable def nibble (w : Nat → ZMod babyBearModulus) (operand : Fin 6) (digit : Fin 16) :
    ZMod babyBearModulus :=
  (row w ⟨6 + digit.val, by omega⟩)[operand.val]'(by have := operand.isLt; omega)

theorem packing (w : Nat → ZMod babyBearModulus) (lane : Fin 6) (limb : Fin 4) :
    limbOf w true lane limb =
      nibble w lane ⟨4 * limb.val, by omega⟩ +
        16 * nibble w lane ⟨4 * limb.val + 1, by omega⟩ +
        256 * nibble w lane ⟨4 * limb.val + 2, by omega⟩ +
        4096 * nibble w lane ⟨4 * limb.val + 3, by omega⟩ := by
  apply pack_eq
  fin_cases lane <;> fin_cases limb <;>
    simp only [limbOf, limbColumn, nibble, row_entry, query] <;> (op_index) <;>
    simp [Expression.eval, Verification.environment, writeCol]

theorem nibble_bound {w : Nat → ZMod babyBearModulus} (h : Holds w) (operand : Fin 6) (digit : Fin 16) :
    (nibble w operand digit).val < 16 := by
  have facts := xor_facts h digit
  by_cases input : operand.val < 5
  · exact facts.1 ⟨operand.val, input⟩
  · have same : operand.val = 5 := by have := operand.isLt; omega
    simp only [nibble, same]
    exact facts.2.1

theorem write_limb_value {w : Nat → ZMod babyBearModulus} (h : Holds w) (lane : Fin 6) (limb : Fin 4) :
    (limbOf w true lane limb).val < 65536 ∧
      (limbOf w true lane limb).val =
        (nibble w lane ⟨4 * limb.val, by omega⟩).val +
          16 * ((nibble w lane ⟨4 * limb.val + 1, by omega⟩).val +
            16 * ((nibble w lane ⟨4 * limb.val + 2, by omega⟩).val +
              16 * (nibble w lane ⟨4 * limb.val + 3, by omega⟩).val)) := by
  have h0 := nibble_bound h lane ⟨4 * limb.val, by omega⟩
  have h1 := nibble_bound h lane ⟨4 * limb.val + 1, by omega⟩
  have h2 := nibble_bound h lane ⟨4 * limb.val + 2, by omega⟩
  have h3 := nibble_bound h lane ⟨4 * limb.val + 3, by omega⟩
  have value := value_of_nibbles h0 h1 h2 h3 (packing w lane limb)
  exact ⟨by rw [value]; omega, value⟩

theorem nibble_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (digit : Fin 16) :
    (nibble w 5 digit).val = (nibble w 0 digit).val ^^^ (nibble w 1 digit).val ^^^
      (nibble w 2 digit).val ^^^ (nibble w 3 digit).val ^^^ (nibble w 4 digit).val :=
  (xor_facts h digit).2.2

theorem write_limb_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (limb : Fin 4) :
    (limbOf w true 5 limb).val = (limbOf w true 0 limb).val ^^^ (limbOf w true 1 limb).val ^^^
      (limbOf w true 2 limb).val ^^^ (limbOf w true 3 limb).val ^^^ (limbOf w true 4 limb).val := by
  let digit (i : Fin 4) : Fin 16 := ⟨4 * limb.val + i.val, by have := i.isLt; omega⟩
  let value (lane : Fin 6) (i : Fin 4) := (nibble w lane (digit i)).val
  have bounds (lane : Fin 6) (i : Fin 4) : value lane i < 2 ^ 4 := nibble_bound h lane (digit i)
  have packed (lane : Fin 6) : (limbOf w true lane limb).val = packFourChunks 4 (value lane) :=
    (write_limb_value h lane limb).2
  rw [packed 5, packed 0, packed 1, packed 2, packed 3, packed 4]
  have outputs : value 5 =
      (fun i => value 0 i ^^^ value 1 i ^^^ value 2 i ^^^ value 3 i ^^^ value 4 i) := by
    funext i
    exact nibble_operation h (digit i)
  rw [outputs]
  exact pack_four_xor_five _ _ _ _ _ (bounds 0) (bounds 1) (bounds 2) (bounds 3) (bounds 4)

/-- The four memory limbs of a lane as one 64-bit value. -/
def laneValue (w : Nat → ZMod babyBearModulus) (writing : Bool) (lane : Fin 6) : Nat :=
  packFourChunks 16 (fun limb => (limbOf w writing lane limb).val)

/-- Lanes 1–4 are readonly: their written limbs are the read ones. -/
theorem readonly_limb (w : Nat → ZMod babyBearModulus) (lane : Fin 4) (limb : Fin 4) :
    limbOf w true ⟨1 + lane.val, by omega⟩ limb = limbOf w false ⟨1 + lane.val, by omega⟩ limb := by
  fin_cases lane <;> fin_cases limb <;> rfl

theorem readonly_lane (w : Nat → ZMod babyBearModulus) (lane : Fin 4) :
    laneValue w true ⟨1 + lane.val, by omega⟩ = laneValue w false ⟨1 + lane.val, by omega⟩ := by
  unfold laneValue
  congr 1
  funext limb
  rw [readonly_limb]

theorem lane_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) :
    laneValue w true 5 = laneValue w true 0 ^^^ laneValue w true 1 ^^^ laneValue w true 2 ^^^
      laneValue w true 3 ^^^ laneValue w true 4 := by
  let value (lane : Fin 6) (limb : Fin 4) := (limbOf w true lane limb).val
  have bounds (lane : Fin 6) (limb : Fin 4) : value lane limb < 2 ^ 16 :=
    (write_limb_value h lane limb).1
  have outputs : value 5 =
      (fun i => value 0 i ^^^ value 1 i ^^^ value 2 i ^^^ value 3 i ^^^ value 4 i) := by
    funext i
    exact write_limb_operation h i
  change packFourChunks 16 (value 5) = _
  rw [outputs]
  exact pack_four_xor_five _ _ _ _ _ (bounds 0) (bounds 1) (bounds 2) (bounds 3) (bounds 4)

end Airbender.Keccak.Split.ColumnParity.Proofs

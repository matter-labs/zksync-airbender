import Human.Circuits.UnifiedReduced.Tables.Setup
import Mathlib.Tactic.IntervalCases

/-! Completeness direction of the unified setup table: explicit row indices for
    the regions an honest witness queries. Each row is computed once, symbolically. -/

namespace Airbender.UnifiedReduced.Completeness
open Verification
set_option warningAsError true

/-- Membership in the unified setup table from an explicit row index. -/
theorem table_contains {p : Nat} [Fact p.Prime] {before : Reference.RiscV.Sail.State}
    {entry : Vector (Expression (ZMod p)) 10} {env : Environment (ZMod p)} (i : Fin 2097537)
    (h : entry.map (Expression.eval env) = (Setup.row before i).map (fun n : Nat => (n : ZMod p))) :
    (Lookup.mk (Setup.table before).toRaw entry).Contains env := by
  change ∃ i : Fin 2097537, entry.map (Expression.eval env) =
    (Setup.row before i).map (fun n : Nat => (n : ZMod p))
  exact ⟨i, h⟩

/-- The byte operation of the wide binary rows, in the table's own form. -/
def byteOp (tag a b : Nat) : Nat :=
  if tag = 4 then (a ^^^ b) % 256 else if tag = 6 then a ||| b else a &&& b

private theorem fixed_row (before : Reference.RiscV.Sail.State) (n : Nat) (h : n < 524545) :
    Setup.row before ⟨n, by omega⟩ = Setup.binaryRow ⟨n, h⟩ := by
  simp only [Setup.row, show n < 1048961 by omega, dite_true, Setup.fixedRow, h]

private theorem split_bytes (a b : Nat) (ha : a < 256) (hb : b < 256) :
    ByteUtils.splitTwoBytes ⟨(a * 256 + b) % 65536, Nat.mod_lt _ (by decide)⟩ =
      (⟨a, ha⟩, ⟨b, hb⟩) := by
  simp only [ByteUtils.splitTwoBytes, Prod.mk.injEq, Fin.mk.injEq]
  omega

/-- Sign rows (tag 3): a byte and its sign-extension byte. -/
theorem sign_row (before : Reference.RiscV.Sail.State) (b : Nat) (hb : b < 256) :
    Setup.row before ⟨1 + b, by omega⟩ =
      #v[b, if b < 128 then 0 else 255, 0, 0, 0, 0, 0, 0, 0, 3] := by
  rw [fixed_row before (1 + b) (by omega)]
  simp only [Setup.binaryRow, shiftBinopRow, show ¬ 1 + b = 0 by omega, show 1 + b < 257 by omega,
    ↓reduceIte, show 1 + b - 1 = b by omega]
  rfl

private theorem binary_byte_row (tag a b : Nat) (ha : a < 256) (hb : b < 256) :
    binaryByteRow tag (a * 256 + b) = #v[a, b, byteOp tag a b, 0, 0, 0, 0, 0, 0, tag] := by
  simp only [binaryByteRow, split_bytes a b ha hb, byteOp]
  rfl

/-- Wide binary rows (XOR/OR/AND tags 4/6/7, stored under IDs 52/53/54). -/
theorem binary_row (before : Reference.RiscV.Sail.State) (tag a b : Nat)
    (valid : tag = 4 ∨ tag = 6 ∨ tag = 7) (ha : a < 256) (hb : b < 256)
    (i : Fin 2097537)
    (hi : i.val = (if tag = 4 then 257 else if tag = 6 then 65793 else 131329) + a * 256 + b) :
    Setup.row before i = #v[a, b, byteOp tag a b, 0, 0, 0, 0, 0, 0, Setup.binaryTag tag] := by
  have k := Nat.lt_of_lt_of_le (show a * 256 + b < a * 256 + 256 by omega)
    (show a * 256 + 256 ≤ 65536 by omega)
  obtain ⟨n, hn⟩ := i
  rcases valid with rfl | rfl | rfl
  all_goals
    simp only [Nat.reduceEqDiff, ↓reduceIte] at hi
    subst hi
  · rw [fixed_row before _ (by omega)]
    simp only [↓reduceIte, Setup.binaryRow, shiftBinopRow, show ¬ 257 + a * 256 + b = 0 by omega,
      show ¬ 257 + a * 256 + b < 257 by omega, show 257 + a * 256 + b < 65793 by omega,
      show 257 + a * 256 + b - 257 = a * 256 + b by omega, binary_byte_row _ a b ha hb]
    rfl
  · rw [fixed_row before _ (by omega)]
    simp only [↓reduceIte, Setup.binaryRow, shiftBinopRow, show ¬ 65793 + a * 256 + b = 0 by omega,
      show ¬ 65793 + a * 256 + b < 257 by omega, show ¬ 65793 + a * 256 + b < 65793 by omega,
      show 65793 + a * 256 + b < 131329 by omega,
      show 65793 + a * 256 + b - 65793 = a * 256 + b by omega, binary_byte_row _ a b ha hb]
    rfl
  · rw [fixed_row before _ (by omega)]
    simp only [↓reduceIte, Setup.binaryRow, shiftBinopRow, show ¬ 131329 + a * 256 + b = 0 by omega,
      show ¬ 131329 + a * 256 + b < 257 by omega, show ¬ 131329 + a * 256 + b < 65793 by omega,
      show ¬ 131329 + a * 256 + b < 131329 by omega, show 131329 + a * 256 + b < 196865 by omega,
      show 131329 + a * 256 + b - 131329 = a * 256 + b by omega, binary_byte_row _ a b ha hb]
    rfl

/-- Shift-amount rows (tag 8): two bytes of the second operand and the 5-bit amount. -/
theorem amount_row (before : Reference.RiscV.Sail.State) (a b : Nat) (ha : a < 256) (hb : b < 256)
    (i : Fin 2097537) (hi : i.val = 196865 + a * 256 + b) :
    Setup.row before i = #v[a, b, a % 32, 0, 0, 0, 0, 0, 0, 8] := by
  obtain ⟨n, hn⟩ := i
  simp only at hi
  subst hi
  rw [fixed_row before _ (by omega)]
  simp only [↓reduceIte, Setup.binaryRow, shiftBinopRow, show ¬ 196865 + a * 256 + b = 0 by omega,
    show ¬ 196865 + a * 256 + b < 257 by omega, show ¬ 196865 + a * 256 + b < 65793 by omega,
    show ¬ 196865 + a * 256 + b < 131329 by omega, show ¬ 196865 + a * 256 + b < 196865 by omega,
    show 196865 + a * 256 + b < 262401 by omega,
    show (196865 + a * 256 + b - 196865) % 65536 = (a * 256 + b) % 65536 by omega,
    split_bytes a b ha hb]
  rfl

/-- One byte's shifted contribution, in the table's own form. -/
def contribution (position byte amount operation : Nat) : Nat :=
  (shiftByteContribution position byte amount operation).toNat

/-- Shift contribution rows (tag 9). -/
theorem shift_row (before : Reference.RiscV.Sail.State) (position byte amount operation : Nat)
    (hp : position < 4) (hb : byte < 256) (ha : amount < 32) (ho : operation < 8)
    (i : Fin 2097537)
    (hi : i.val = 262401 + position * 65536 + byte * 256 + amount * 8 + operation) :
    Setup.row before i = #v[position, byte, amount, operation,
      contribution position byte amount operation % 256,
      contribution position byte amount operation / 256 % 256,
      contribution position byte amount operation / 65536 % 256,
      contribution position byte amount operation / 16777216 % 256, 0, 9] := by
  obtain ⟨n, hn⟩ := i
  simp only at hi
  subst hi
  rw [fixed_row before _ (by omega)]
  have key : 262401 + position * 65536 + byte * 256 + amount * 8 + operation - 262401 =
      position * 65536 + byte * 256 + amount * 8 + operation := by omega
  simp only [↓reduceIte, Setup.binaryRow, shiftBinopRow,
    show ¬ 262401 + position * 65536 + byte * 256 + amount * 8 + operation = 0 by omega,
    show ¬ 262401 + position * 65536 + byte * 256 + amount * 8 + operation < 257 by omega,
    show ¬ 262401 + position * 65536 + byte * 256 + amount * 8 + operation < 65793 by omega,
    show ¬ 262401 + position * 65536 + byte * 256 + amount * 8 + operation < 131329 by omega,
    show ¬ 262401 + position * 65536 + byte * 256 + amount * 8 + operation < 196865 by omega,
    show ¬ 262401 + position * 65536 + byte * 256 + amount * 8 + operation < 262401 by omega, key,
    show (position * 65536 + byte * 256 + amount * 8 + operation) / 65536 = position by omega,
    show (position * 65536 + byte * 256 + amount * 8 + operation) / 256 % 256 = byte by omega,
    show (position * 65536 + byte * 256 + amount * 8 + operation) / 8 % 32 = amount by omega,
    show (position * 65536 + byte * 256 + amount * 8 + operation) % 8 = operation by omega]
  rfl

/-- One output byte of the XOR-rotate rows, in the table's own form. -/
def rotated (k a b : Nat) : Nat → Nat
  | 0 => ((BitVec.ofNat 32 (a ^^^ b)).rotateRight (#[16, 12, 8, 7][k]!)).toNat % 256
  | 1 => ((BitVec.ofNat 32 (a ^^^ b)).rotateRight (#[16, 12, 8, 7][k]!)).toNat / 256 % 256
  | 2 => ((BitVec.ofNat 32 (a ^^^ b)).rotateRight (#[16, 12, 8, 7][k]!)).toNat / 65536 % 256
  | _ => ((BitVec.ofNat 32 (a ^^^ b)).rotateRight (#[16, 12, 8, 7][k]!)).toNat / 16777216 % 256

private theorem rotate_entry (k a b : Nat) (ha : a < 256) (hb : b < 256)
    (h : k * 65536 + a * 256 + b < 262144) :
    Setup.rotateRow ⟨k * 65536 + a * 256 + b, h⟩ = #v[a, b, rotated k a b 0, rotated k a b 1,
      rotated k a b 2, rotated k a b 3, 0, 0, 0, 47 + k] := by
  simp only [Setup.rotateRow, show (k * 65536 + a * 256 + b) / 65536 = k by omega,
    show (k * 65536 + a * 256 + b) / 256 % 256 = a by omega,
    show (k * 65536 + a * 256 + b) % 256 = b by omega]
  rfl

/-- XOR-rotate rows (IDs 47-50). -/
theorem rotate_row (before : Reference.RiscV.Sail.State) (k a b : Nat) (hk : k < 4) (ha : a < 256)
    (hb : b < 256) (i : Fin 2097537) (hi : i.val = 786817 + k * 65536 + a * 256 + b) :
    Setup.row before i = #v[a, b, rotated k a b 0, rotated k a b 1, rotated k a b 2,
      rotated k a b 3, 0, 0, 0, 47 + k] := by
  obtain ⟨n, hn⟩ := i
  simp only at hi
  subst hi
  have hfix : 786817 + k * 65536 + a * 256 + b < 1048961 := by omega
  rw [← rotate_entry k a b ha hb (by omega)]
  simp only [Setup.row, hfix, dite_true, Setup.fixedRow,
    show ¬ 786817 + k * 65536 + a * 256 + b < 524545 by omega, dite_false,
    show ¬ 786817 + k * 65536 + a * 256 + b < 655617 by omega,
    show ¬ 786817 + k * 65536 + a * 256 + b < 721153 by omega,
    show ¬ 786817 + k * 65536 + a * 256 + b < 786689 by omega,
    show ¬ 786817 + k * 65536 + a * 256 + b < 786817 by omega, ↓reduceIte]
  exact congrArg Setup.rotateRow
    (Fin.ext (show 786817 + k * 65536 + a * 256 + b - 786817 = k * 65536 + a * 256 + b by omega))

theorem row_fixed (before : Reference.RiscV.Sail.State) (n : Nat) (hn : n < 2097537)
    (h1 : n < 1048961) : Setup.row before ⟨n, hn⟩ = Setup.fixedRow ⟨n, h1⟩ := dite_eq_left h1

/-- Zero-test rows (tag 1). -/
theorem zero_row (before : Reference.RiscV.Sail.State) (key : Nat) (hk : key < 131072)
    (i : Fin 2097537) (hi : i.val = 524545 + key) :
    Setup.row before i = #v[key, if key = 0 then 1 else 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  obtain ⟨n, hn⟩ := i
  simp only at hi
  rw [row_fixed before n hn (by omega)]
  have e : Setup.fixedRow ⟨n, by omega⟩ =
      #v[n - 524545, if n - 524545 = 0 then 1 else 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
    unfold Setup.fixedRow
    rw [dite_eq_right (show ¬ n < 524545 by omega), ite_eq_left (show n < 655617 by omega)]
  rw [e, show n - 524545 = key by omega]

/-- Limb-sign rows (tag 5). -/
theorem sign16_row (before : Reference.RiscV.Sail.State) (key : Nat) (hk : key < 65536)
    (i : Fin 2097537) (hi : i.val = 655617 + key) :
    Setup.row before i = #v[key, key / 32768, 0, 0, 0, 0, 0, 0, 0, 5] := by
  obtain ⟨n, hn⟩ := i
  simp only at hi
  rw [row_fixed before n hn (by omega)]
  have e : Setup.fixedRow ⟨n, by omega⟩ = #v[n - 655617, (n - 655617) / 32768, 0, 0, 0, 0, 0, 0, 0, 5] := by
    unfold Setup.fixedRow
    rw [dite_eq_right (show ¬ n < 524545 by omega), ite_eq_right (show ¬ n < 655617 by omega),
      ite_eq_left (show n < 721153 by omega)]
  rw [e, show n - 655617 = key by omega]

/-- Jump-target cleanup rows (tag 2). -/
theorem cleanup_row (before : Reference.RiscV.Sail.State) (key : Nat) (hk : key < 65536)
    (i : Fin 2097537) (hi : i.val = 721153 + key) :
    Setup.row before i = #v[key, key / 2 % 2, key - key % 4, 0, 0, 0, 0, 0, 0, 2] := by
  obtain ⟨n, hn⟩ := i
  simp only at hi
  rw [row_fixed before n hn (by omega)]
  have e : Setup.fixedRow ⟨n, by omega⟩ =
      #v[n - 721153, (n - 721153) / 2 % 2, n - 721153 - (n - 721153) % 4, 0, 0, 0, 0, 0, 0, 2] := by
    unfold Setup.fixedRow
    rw [dite_eq_right (show ¬ n < 524545 by omega), ite_eq_right (show ¬ n < 655617 by omega),
      ite_eq_right (show ¬ n < 721153 by omega), ite_eq_left (show n < 786689 by omega)]
  rw [e, show n - 721153 = key by omega]

/-- Conditional-resolution rows (tag 51). -/
theorem condition_row (before : Reference.RiscV.Sail.State) (key : Nat) (hk : key < 128)
    (i : Fin 2097537) (hi : i.val = 786689 + key) :
    Setup.row before i =
      #v[key, conditionalValue (Setup.conditionalKey key), 0, 0, 0, 0, 0, 0, 0, 51] := by
  obtain ⟨n, hn⟩ := i
  simp only at hi
  rw [row_fixed before n hn (by omega)]
  have e : Setup.fixedRow ⟨n, by omega⟩ = #v[n - 786689,
      conditionalValue (Setup.conditionalKey (n - 786689)), 0, 0, 0, 0, 0, 0, 0, 51] := by
    unfold Setup.fixedRow
    rw [dite_eq_right (show ¬ n < 524545 by omega), ite_eq_right (show ¬ n < 655617 by omega),
      ite_eq_right (show ¬ n < 721153 by omega), ite_eq_right (show ¬ n < 786689 by omega),
      ite_eq_left (show n < 786817 by omega)]
  rw [e, show n - 786689 = key by omega]

/-- Membership from an explicit row, checked column by column. -/
theorem table_contains_row {p : Nat} [Fact p.Prime] {before : Reference.RiscV.Sail.State}
    {entry : Vector (Expression (ZMod p)) 10} {env : Environment (ZMod p)} (i : Fin 2097537)
    (v : Vector Nat 10) (hrow : Setup.row before i = v)
    (h0 : entry[0].eval env = (v[0] : ZMod p)) (h1 : entry[1].eval env = (v[1] : ZMod p))
    (h2 : entry[2].eval env = (v[2] : ZMod p)) (h3 : entry[3].eval env = (v[3] : ZMod p))
    (h4 : entry[4].eval env = (v[4] : ZMod p)) (h5 : entry[5].eval env = (v[5] : ZMod p))
    (h6 : entry[6].eval env = (v[6] : ZMod p)) (h7 : entry[7].eval env = (v[7] : ZMod p))
    (h8 : entry[8].eval env = (v[8] : ZMod p)) (h9 : entry[9].eval env = (v[9] : ZMod p)) :
    (Lookup.mk (Setup.table before).toRaw entry).Contains env := by
  refine table_contains i ?_
  rw [hrow]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_map]
  interval_cases j <;> assumption

end Airbender.UnifiedReduced.Completeness

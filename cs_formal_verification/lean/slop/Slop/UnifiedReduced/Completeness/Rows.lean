import Human.Circuits.UnifiedReduced.Tables.Setup
import Mathlib.Tactic.IntervalCases

/-! Completeness direction of the unified setup table: explicit row indices for
    the regions an honest witness queries. Each row is computed once, symbolically. -/

namespace Airbender.UnifiedReduced.Completeness
open Verification
set_option warningAsError true

/-- The byte operation of the wide binary rows, in the table's own form. -/
def byteOp (tag a b : Nat) : Nat :=
  if tag = 4 then (a ^^^ b) % 256 else if tag = 6 then a ||| b else a &&& b

private theorem split_bytes (a b : Nat) (ha : a < 256) (hb : b < 256) :
    ByteUtils.splitTwoBytes ⟨(a * 256 + b) % 65536, Nat.mod_lt _ (by decide)⟩ =
      (⟨a, ha⟩, ⟨b, hb⟩) := by
  simp only [ByteUtils.splitTwoBytes, Prod.mk.injEq, Fin.mk.injEq]
  omega

private theorem binary_byte_row (tag a b : Nat) (ha : a < 256) (hb : b < 256) :
    binaryByteRow tag (a * 256 + b) = #v[a, b, byteOp tag a b, 0, 0, 0, 0, 0, 0, tag] := by
  simp only [binaryByteRow, split_bytes a b ha hb, byteOp]
  rfl

/-- One byte's shifted contribution, in the table's own form. -/
def contribution (position byte amount operation : Nat) : Nat :=
  (shiftByteContribution position byte amount operation).toNat

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

end Airbender.UnifiedReduced.Completeness

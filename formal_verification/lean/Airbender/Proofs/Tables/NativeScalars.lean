import Airbender.Review.Helpers.Tables.NativeScalarData
import Airbender.Proofs.Mersenne31
import Airbender.Proofs.Constraints

namespace Airbender.Verification.NativeSetup.Proofs
open Setup

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

/-- Symbolic actual data access; neither scalar table is evaluated row by row. -/
private theorem affine_row (length offset : Nat) (i : Fin length) :
    (⟨length, offset, #v[⟨#[.affine length 0 1]⟩]⟩ : TableData 1).rowNat i = #v[i.val] := by
  have column : (⟨#[.affine length 0 1]⟩ : Column).get? i.val = some i.val := by
    change getFromBlocks [.affine length 0 1] i.val = _
    rw [getFromBlocks]
    simp only [Block.length]
    rw [if_pos i.isLt]
    simpa using affine_get length 0 1 i.val i.isLt
  ext k bound
  have zero : k = 0 := by omega
  subst k
  simp [TableData.rowNat, column]

theorem scalar_lengths (kind : ScalarKind) : kind.data.length = 2 ^ kind.bits := by
  cases kind <;> rfl

theorem exported_scalar_rows (kind : ScalarKind) (i : Fin kind.data.length) :
    kind.data.rowNat i = #v[i.val] := by
  cases kind
  · exact affine_row 65536 0 i
  · exact affine_row 524288 1 i

/-- Every active row has the native prefix value or zero filler, with no
    table-equivalence premise and no materialized 2^24-row certificate. -/
theorem active_scalar_rows {p : Nat} (kind : ScalarKind) (row : Row) :
    scalarRow (p := p) kind row = if row.val < 2 ^ kind.bits then (row.val : ZMod p) else 0 := by
  unfold scalarRow
  by_cases present : row.val < kind.data.length
  · have small : row.val < 2 ^ kind.bits := by simpa only [scalar_lengths] using present
    rw [dif_pos present, if_pos small]
    simp [TableData.row, exported_scalar_rows]
  · have large : ¬row.val < 2 ^ kind.bits := by simpa only [scalar_lengths] using present
    rw [dif_neg present, if_neg large]

theorem scalar_padding_zero {p : Nat} (kind : ScalarKind) (row : Row)
    (padding : 2 ^ kind.bits ≤ row.val) : scalarRow (p := p) kind row = 0 := by
  rw [active_scalar_rows, if_neg (by omega)]

/-- Actual native scalar prefixes and their modeled zero fill have exactly the
    canonical range meanings used by both imported circuit families. -/
theorem scalar_lookup (kind : ScalarKind) (value : ZMod mersenne31Modulus) :
    ScalarContains kind value ↔ value.val < 2 ^ kind.bits := by
  constructor
  · rintro ⟨row, same⟩
    rw [active_scalar_rows] at same
    split_ifs at same with present
    · rw [← same, ZMod.val_natCast]
      exact lt_of_le_of_lt (Nat.mod_le _ _) present
    · rw [← same, ZMod.val_zero]
      exact Nat.two_pow_pos _
  · intro bound
    have extent : 2 ^ kind.bits ≤ 16777215 := by cases kind <;> decide
    refine ⟨⟨value.val, by omega⟩, ?_⟩
    rw [active_scalar_rows, if_pos bound, ZMod.natCast_zmod_val]

/-- Connect the certified scalar rows to the unchanged native Clean helpers. -/
theorem range16_lookup {entry : Expression (ZMod mersenne31Modulus)}
    {env : _root_.Environment (ZMod mersenne31Modulus)} :
    ScalarContains .range16 (entry.eval env) ↔ (Verification.range16 entry).Contains env := by
  constructor
  · intro member
    exact range16_contains ((scalar_lookup .range16 _).mp member)
  · intro member
    exact (scalar_lookup .range16 _).mpr (range16_bound member)

theorem timestamp19_lookup {entry : Expression (ZMod mersenne31Modulus)}
    {env : _root_.Environment (ZMod mersenne31Modulus)} :
    ScalarContains .timestamp19 (entry.eval env) ↔ (Verification.timestamp19 entry).Contains env := by
  constructor
  · intro member
    exact timestamp19_contains ((scalar_lookup .timestamp19 _).mp member)
  · intro member
    exact (scalar_lookup .timestamp19 _).mpr (timestamp19_bound member)

end Airbender.Verification.NativeSetup.Proofs

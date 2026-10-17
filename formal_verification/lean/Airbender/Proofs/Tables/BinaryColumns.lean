import Airbender.Review.Helpers.Tables.Shift.XorData
import Airbender.Review.Helpers.Tables.Shift.OrData
import Airbender.Review.Helpers.Tables.Shift.AndData
import Airbender.Review.Helpers.Tables.Shift.TruncateData
import Mathlib.Tactic.FinCases

namespace Airbender.Verification.BinaryColumns
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def data (kind : Fin 4) : TableData 10 :=
  #v[byteXorData, byteOrData, byteAndData, byteTruncateData][kind]
def region (kind : Fin 4) : Region :=
  #v[byteXorDataRegion, byteOrDataRegion, byteAndDataRegion, byteTruncateDataRegion][kind]

theorem periodic_constant (count first n : Nat) (bound : n < count * 256) :
    Block.get? (.periodic count 1 (Array.replicate 256 first)) n =
      some (first + n / 256) := by
  have hm : n % 256 < 256 := Nat.mod_lt _ (by decide)
  simp [Block.get?, Block.length, bound, hm]
  simpa only [Int.natCast_add, Int.natCast_ediv, Nat.cast_ofNat] using
    And.intro (Int.natCast_nonneg (first + n / 256)) (Int.toNat_natCast (first + n / 256))

theorem first (kind : Fin 4) (n : Nat) (bound : n < 65536) :
    (data kind).columns[0].get? n = some (n / 256) := by
  have column : (data kind).columns[0] =
      Column.mk #[.periodic 256 1 (Array.replicate 256 0)] := by
    fin_cases kind <;> rfl
  rw [column]
  simp only [Column.get?, getFromBlocks, Block.length, Array.size_replicate,
    Nat.reduceMul, if_pos bound]
  simpa only [Nat.zero_add] using periodic_constant 256 0 n bound

theorem second (kind : Fin 4) (n : Nat) (bound : n < 65536) :
    (data kind).columns[1].get? n = some (n % 256) := by
  have column : (data kind).columns[1] =
      Column.mk #[.periodic 256 0 (Array.range 256)] := by
    fin_cases kind <;> rfl
  rw [column]
  have hm : n % 256 < 256 := Nat.mod_lt _ (by decide)
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound, hm]
  simpa only [Int.natCast_emod, Nat.cast_ofNat] using
    And.intro (Int.natCast_nonneg (n % 256)) (Int.toNat_natCast (n % 256))

theorem padding (kind : Fin 4) (lane : Fin 6) (n : Nat) (bound : n < 65536) :
    (data kind).columns[lane.val + 3].get? n = some 0 := by
  have column : (data kind).columns[lane.val + 3] = Column.mk #[.affine 65536 0 0] := by
    fin_cases kind <;> fin_cases lane <;> rfl
  rw [column]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound]

theorem tag (kind : Fin 4) (n : Nat) (bound : n < 65536) :
    (data kind).columns[9].get? n = some (region kind).id := by
  have column : (data kind).columns[9] = Column.mk #[.affine 65536 (region kind).id 0] := by
    fin_cases kind <;> rfl
  rw [column]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound]

end Airbender.Verification.BinaryColumns

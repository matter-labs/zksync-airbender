import Airbender.Review.Circuits.UnifiedReduced.Tables.Setup

namespace Airbender.Compiler.UnifiedLogicalRegions
open Airbender
open Airbender.UnifiedReduced.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem region0_row (index : Fin 1) :
    importedRow ⟨0 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨0, by decide⟩ index.val := by
  have zero : index = ⟨0, by decide⟩ := by
    apply Fin.ext
    change index.val = 0
    have := index.isLt
    omega
  rw [zero]
  rfl

theorem region1_row (index : Fin 256) :
    importedRow ⟨1 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨1, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (1 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_pos (by change (1 + index.val) < 524545; omega)]
  unfold binaryRow
  rw [if_neg (by change ¬(1 + index.val) < 1; omega)]
  rw [if_pos (by change (1 + index.val) < 257; omega)]
  have shifted : (1 + index.val) - logicalFixedOffset 1 = index.val := by
    change (1 + index.val) - 1 = index.val
    omega
  rw [shifted]
  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)

theorem region2_row (index : Fin 65536) :
    importedRow ⟨257 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨2, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (257 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_pos (by change (257 + index.val) < 524545; omega)]
  unfold binaryRow
  rw [if_neg (by change ¬(257 + index.val) < 1; omega)]
  rw [if_neg (by change ¬(257 + index.val) < 257; omega)]
  rw [if_pos (by change (257 + index.val) < 65793; omega)]
  have shifted : (257 + index.val) - logicalFixedOffset 2 = index.val := by
    change (257 + index.val) - 257 = index.val
    omega
  rw [shifted]
  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)

theorem region3_row (index : Fin 65536) :
    importedRow ⟨65793 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨3, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (65793 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_pos (by change (65793 + index.val) < 524545; omega)]
  unfold binaryRow
  rw [if_neg (by change ¬(65793 + index.val) < 1; omega)]
  rw [if_neg (by change ¬(65793 + index.val) < 257; omega)]
  rw [if_neg (by change ¬(65793 + index.val) < 65793; omega)]
  rw [if_pos (by change (65793 + index.val) < 131329; omega)]
  have shifted : (65793 + index.val) - logicalFixedOffset 3 = index.val := by
    change (65793 + index.val) - 65793 = index.val
    omega
  rw [shifted]
  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)

theorem region4_row (index : Fin 65536) :
    importedRow ⟨131329 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨4, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (131329 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_pos (by change (131329 + index.val) < 524545; omega)]
  unfold binaryRow
  rw [if_neg (by change ¬(131329 + index.val) < 1; omega)]
  rw [if_neg (by change ¬(131329 + index.val) < 257; omega)]
  rw [if_neg (by change ¬(131329 + index.val) < 65793; omega)]
  rw [if_neg (by change ¬(131329 + index.val) < 131329; omega)]
  rw [if_pos (by change (131329 + index.val) < 196865; omega)]
  have shifted : (131329 + index.val) - logicalFixedOffset 4 = index.val := by
    change (131329 + index.val) - 131329 = index.val
    omega
  rw [shifted]
  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)

theorem region5_row (index : Fin 65536) :
    importedRow ⟨196865 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨5, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (196865 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_pos (by change (196865 + index.val) < 524545; omega)]
  unfold binaryRow
  rw [if_neg (by change ¬(196865 + index.val) < 1; omega)]
  rw [if_neg (by change ¬(196865 + index.val) < 257; omega)]
  rw [if_neg (by change ¬(196865 + index.val) < 65793; omega)]
  rw [if_neg (by change ¬(196865 + index.val) < 131329; omega)]
  rw [if_neg (by change ¬(196865 + index.val) < 196865; omega)]
  rw [if_pos (by change (196865 + index.val) < 262401; omega)]
  have shifted : (196865 + index.val) - logicalFixedOffset 5 = index.val := by
    change (196865 + index.val) - 196865 = index.val
    omega
  rw [shifted]
  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)

theorem region6_row (index : Fin 262144) :
    importedRow ⟨262401 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨6, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (262401 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_pos (by change (262401 + index.val) < 524545; omega)]
  unfold binaryRow
  rw [if_neg (by change ¬(262401 + index.val) < 1; omega)]
  rw [if_neg (by change ¬(262401 + index.val) < 257; omega)]
  rw [if_neg (by change ¬(262401 + index.val) < 65793; omega)]
  rw [if_neg (by change ¬(262401 + index.val) < 131329; omega)]
  rw [if_neg (by change ¬(262401 + index.val) < 196865; omega)]
  rw [if_neg (by change ¬(262401 + index.val) < 262401; omega)]
  have shifted : (262401 + index.val) - logicalFixedOffset 6 = index.val := by
    change (262401 + index.val) - 262401 = index.val
    omega
  rw [shifted]
  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)

theorem region7_row (index : Fin 131072) :
    importedRow ⟨524545 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨7, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (524545 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_neg (by change ¬(524545 + index.val) < 524545; omega)]
  rw [if_pos (by change (524545 + index.val) < 655617; omega)]
  have shifted : (524545 + index.val) - logicalFixedOffset 7 = index.val := by
    change (524545 + index.val) - 524545 = index.val
    omega
  rw [shifted]
  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)

theorem region8_row (index : Fin 65536) :
    importedRow ⟨655617 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨8, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (655617 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_neg (by change ¬(655617 + index.val) < 524545; omega)]
  rw [if_neg (by change ¬(655617 + index.val) < 655617; omega)]
  rw [if_pos (by change (655617 + index.val) < 721153; omega)]
  have shifted : (655617 + index.val) - logicalFixedOffset 8 = index.val := by
    change (655617 + index.val) - 655617 = index.val
    omega
  rw [shifted]
  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)

theorem region9_row (index : Fin 65536) :
    importedRow ⟨721153 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨9, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (721153 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_neg (by change ¬(721153 + index.val) < 524545; omega)]
  rw [if_neg (by change ¬(721153 + index.val) < 655617; omega)]
  rw [if_neg (by change ¬(721153 + index.val) < 721153; omega)]
  rw [if_pos (by change (721153 + index.val) < 786689; omega)]
  have shifted : (721153 + index.val) - logicalFixedOffset 9 = index.val := by
    change (721153 + index.val) - 721153 = index.val
    omega
  rw [shifted]
  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)

theorem region10_row (index : Fin 128) :
    importedRow ⟨786689 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨10, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (786689 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_neg (by change ¬(786689 + index.val) < 524545; omega)]
  rw [if_neg (by change ¬(786689 + index.val) < 655617; omega)]
  rw [if_neg (by change ¬(786689 + index.val) < 721153; omega)]
  rw [if_neg (by change ¬(786689 + index.val) < 786689; omega)]
  rw [if_pos (by change (786689 + index.val) < 786817; omega)]
  have shifted : (786689 + index.val) - logicalFixedOffset 10 = index.val := by
    change (786689 + index.val) - 786689 = index.val
    omega
  rw [shifted]
  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)

theorem region11_row (index : Fin 65536) :
    importedRow ⟨786817 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨11, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (786817 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_neg (by change ¬(786817 + index.val) < 524545; omega)]
  rw [if_neg (by change ¬(786817 + index.val) < 655617; omega)]
  rw [if_neg (by change ¬(786817 + index.val) < 721153; omega)]
  rw [if_neg (by change ¬(786817 + index.val) < 786689; omega)]
  rw [if_neg (by change ¬(786817 + index.val) < 786817; omega)]
  unfold rotateRow
  have quotient : ((786817 + index.val) - logicalFixedOffset 11) / 65536 = 0 := by
    change ((786817 + index.val) - 786817) / 65536 = 0
    omega
  have remainder : ((786817 + index.val) - logicalFixedOffset 11) % 65536 = index.val := by
    change ((786817 + index.val) - 786817) % 65536 = index.val
    omega
  apply congrArg₂ nativeFixedRow
  · apply Fin.ext
    change 11 + (((786817 + index.val) - logicalFixedOffset 11) / 65536) = 11
    rw [quotient]
  · exact remainder

theorem region12_row (index : Fin 65536) :
    importedRow ⟨852353 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨12, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (852353 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_neg (by change ¬(852353 + index.val) < 524545; omega)]
  rw [if_neg (by change ¬(852353 + index.val) < 655617; omega)]
  rw [if_neg (by change ¬(852353 + index.val) < 721153; omega)]
  rw [if_neg (by change ¬(852353 + index.val) < 786689; omega)]
  rw [if_neg (by change ¬(852353 + index.val) < 786817; omega)]
  unfold rotateRow
  have quotient : ((852353 + index.val) - logicalFixedOffset 11) / 65536 = 1 := by
    change ((852353 + index.val) - 786817) / 65536 = 1
    omega
  have remainder : ((852353 + index.val) - logicalFixedOffset 11) % 65536 = index.val := by
    change ((852353 + index.val) - 786817) % 65536 = index.val
    omega
  apply congrArg₂ nativeFixedRow
  · apply Fin.ext
    change 11 + (((852353 + index.val) - logicalFixedOffset 11) / 65536) = 12
    rw [quotient]
  · exact remainder

theorem region13_row (index : Fin 65536) :
    importedRow ⟨917889 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨13, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (917889 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_neg (by change ¬(917889 + index.val) < 524545; omega)]
  rw [if_neg (by change ¬(917889 + index.val) < 655617; omega)]
  rw [if_neg (by change ¬(917889 + index.val) < 721153; omega)]
  rw [if_neg (by change ¬(917889 + index.val) < 786689; omega)]
  rw [if_neg (by change ¬(917889 + index.val) < 786817; omega)]
  unfold rotateRow
  have quotient : ((917889 + index.val) - logicalFixedOffset 11) / 65536 = 2 := by
    change ((917889 + index.val) - 786817) / 65536 = 2
    omega
  have remainder : ((917889 + index.val) - logicalFixedOffset 11) % 65536 = index.val := by
    change ((917889 + index.val) - 786817) % 65536 = index.val
    omega
  apply congrArg₂ nativeFixedRow
  · apply Fin.ext
    change 11 + (((917889 + index.val) - logicalFixedOffset 11) / 65536) = 13
    rw [quotient]
  · exact remainder

theorem region14_row (index : Fin 65536) :
    importedRow ⟨983425 + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨14, by decide⟩ index.val := by
  have bound := index.isLt
  unfold importedRow
  rw [dif_pos (by change (983425 + index.val) < 1048961; omega)]
  unfold fixedRow
  rw [dif_neg (by change ¬(983425 + index.val) < 524545; omega)]
  rw [if_neg (by change ¬(983425 + index.val) < 655617; omega)]
  rw [if_neg (by change ¬(983425 + index.val) < 721153; omega)]
  rw [if_neg (by change ¬(983425 + index.val) < 786689; omega)]
  rw [if_neg (by change ¬(983425 + index.val) < 786817; omega)]
  unfold rotateRow
  have quotient : ((983425 + index.val) - logicalFixedOffset 11) / 65536 = 3 := by
    change ((983425 + index.val) - 786817) / 65536 = 3
    omega
  have remainder : ((983425 + index.val) - logicalFixedOffset 11) % 65536 = index.val := by
    change ((983425 + index.val) - 786817) % 65536 = index.val
    omega
  apply congrArg₂ nativeFixedRow
  · apply Fin.ext
    change 11 + (((983425 + index.val) - logicalFixedOffset 11) / 65536) = 14
    rw [quotient]
  · exact remainder

end Airbender.Compiler.UnifiedLogicalRegions

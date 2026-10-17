import Airbender.Proofs.Tables.ImportedPairs
import Airbender.Proofs.Tables.ImportedControl
import Airbender.Proofs.Tables.ImportedCleanup
import Mathlib.Tactic.FinCases

namespace Airbender.Verification.ImportedPairRows
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private def pairData (kind : Fin 3) : TableData 10 :=
  #v[regZeroData, signData, conditionalData][kind]
private def pairRegion (kind : Fin 3) : Region :=
  #v[regZeroDataRegion, signDataRegion, conditionalDataRegion][kind]
private def pairValue (kind : Fin 3) (key : Nat) : Nat :=
  if kind.val = 0 then (if key = 0 then 1 else 0)
  else if kind.val = 1 then key / 32768 else conditionalValue key

private theorem constant_get (length value n : Nat) (bound : n < length) :
    (Column.mk #[.affine length value 0]).get? n = some value := by
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound]

private theorem pair_padding (kind : Fin 3) (lane : Fin 7)
    (index : Fin (pairData kind).length) :
    (pairData kind).columns[lane.val + 2].get? index.val = some 0 := by
  have column : (pairData kind).columns[lane.val + 2] =
      Column.mk #[.affine (pairData kind).length 0 0] := by
    fin_cases kind <;> fin_cases lane <;> rfl
  rw [column]
  exact constant_get _ _ _ index.isLt

private theorem pair_tag (kind : Fin 3) (index : Fin (pairData kind).length) :
    (pairData kind).columns[9].get? index.val = some (pairRegion kind).id := by
  have column : (pairData kind).columns[9] =
      Column.mk #[.affine (pairData kind).length (pairRegion kind).id 0] := by
    fin_cases kind <;> rfl
  rw [column]
  exact constant_get _ _ _ index.isLt

/-- Native IDs 1/5/31: meaningful fields, every padding column and the tag. -/
theorem jump_pair_columns (kind : Fin 3) (index : Fin (pairData kind).length) :
    setupPairRow (pairData kind) (by decide) index =
        (index.val, pairValue kind index.val) ∧
      (∀ lane : Fin 7, (pairData kind).columns[lane.val + 2].get? index.val = some 0) ∧
      (pairData kind).columns[9].get? index.val = some (pairRegion kind).id := by
  refine ⟨?_, fun lane => pair_padding kind lane index, pair_tag kind index⟩
  fin_cases kind
  · exact ImportedPairs.regZero_row index
  · exact ImportedPairs.sign_row index
  · exact ImportedControl.conditional_row index

/-- The projection retains the exact exported physical region geometry. -/
theorem jump_pair_geometry (kind : Fin 3) :
    (pairData kind).length = (pairRegion kind).length ∧ (pairData kind).offset = 0 := by
  fin_cases kind <;> exact ⟨rfl, rfl⟩

/-- All nine physical columns of native mul/div ID 41. -/
theorem low_byte_columns (index : Fin 65536) :
    setupPairRow lowByteData (by decide) index = (index.val, index.val % 256) ∧
      (∀ lane : Fin 6, lowByteData.columns[lane.val + 2].get? index.val = some 0) ∧
      lowByteData.columns[8].get? index.val = some lowByteDataRegion.id := by
  refine ⟨ImportedPairs.lowByte_row index, ?_, ?_⟩
  · intro lane
    have column : lowByteData.columns[lane.val + 2] =
        Column.mk #[.affine 65536 0 0] := by fin_cases lane <;> rfl
    rw [column]
    exact constant_get _ _ _ index.isLt
  · change (Column.mk #[.affine 65536 41 0]).get? index.val = some 41
    exact constant_get _ _ _ index.isLt

/-- All ten physical columns of the JALR cleanup region, native ID 2. -/
theorem cleanup_columns (index : Fin 65536) :
    setupTripleRow jumpCleanupData (by decide) index =
        (index.val, index.val / 2 % 2, index.val - index.val % 4) ∧
      (∀ lane : Fin 6, jumpCleanupData.columns[lane.val + 3].get? index.val = some 0) ∧
      jumpCleanupData.columns[9].get? index.val = some jumpCleanupDataRegion.id := by
  refine ⟨ImportedCleanup.cleanup_row index, ?_, ?_⟩
  · intro lane
    have column : jumpCleanupData.columns[lane.val + 3] =
        Column.mk #[.affine 65536 0 0] := by fin_cases lane <;> rfl
    rw [column]
    exact constant_get _ _ _ index.isLt
  · change (Column.mk #[.affine 65536 2 0]).get? index.val = some 2
    exact constant_get _ _ _ index.isLt

/-- Clean's projected fields are exactly the imported native field columns. -/
theorem pair_native_cast (data : TableData width) (wide : 2 ≤ width)
    (index : Fin data.length) :
    (((setupPairRow data wide index).1 : ZMod babyBearModulus),
      ((setupPairRow data wide index).2 : ZMod babyBearModulus)) =
    (((data.row index)[0]'(by omega) : ZMod babyBearModulus),
      ((data.row index)[1]'(by omega) : ZMod babyBearModulus)) := by
  simp [setupPairRow, TableData.row, signedValue_cast]

/-- The cleanup projection likewise preserves all three native field columns. -/
theorem triple_native_cast (data : TableData width) (wide : 3 ≤ width)
    (index : Fin data.length) :
    (((setupTripleRow data wide index).1 : ZMod babyBearModulus),
      ((setupTripleRow data wide index).2.1 : ZMod babyBearModulus),
      ((setupTripleRow data wide index).2.2 : ZMod babyBearModulus)) =
    (((data.row index)[0]'(by omega) : ZMod babyBearModulus),
      ((data.row index)[1]'(by omega) : ZMod babyBearModulus),
      ((data.row index)[2]'(by omega) : ZMod babyBearModulus)) := by
  simp [setupTripleRow, TableData.row, signedValue_cast]

end Airbender.Verification.ImportedPairRows

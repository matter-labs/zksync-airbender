import Airbender.Proofs.GKRProtocol.ColumnSlices
import Airbender.Review.Helpers.Tables.PairData

namespace Airbender.Compiler
open Airbender
set_option warningAsError true

theorem materialized_pair_contains (native : MaterializedLookupSetup width)
    (data : Setup.TableData targetWidth) (sourceWide : 2 ≤ width) (targetWide : 2 ≤ targetWidth)
    (offset : Nat) (sourceOffset : native.imported.data.offset = 0) (targetOffset : data.offset = 0)
    (row : Fin native.imported.data.length) (index : Fin data.length)
    (position : row.val = offset + index.val)
    (firstColumn : ∀ entry : Fin data.length,
      native.imported.data.columns[(0 : Nat)].get? (offset + entry.val) = data.columns[(0 : Nat)].get? entry.val)
    (secondColumn : ∀ entry : Fin data.length,
      native.imported.data.columns[(1 : Nat)].get? (offset + entry.val) = data.columns[(1 : Nat)].get? entry.val)
    (name : String) (provided : Array (Source.BaseField × Source.BaseField)) :
    (Verification.setupPairTable (p := babyBearModulus) name data targetWide).Contains provided
      (native.value row (.generic 0), native.value row (.generic 1)) := by
  change ∃ entry : Fin data.length,
    (native.value row (.generic 0), native.value row (.generic 1)) =
      (((Verification.setupPairRow data targetWide entry).1 : Source.BaseField),
        ((Verification.setupPairRow data targetWide entry).2 : Source.BaseField))
  refine ⟨index, Prod.ext ?_ ?_⟩
  · rw [native.generic_cell_value row (⟨0, by omega⟩ : Fin width), sourceOffset, Nat.zero_add,
      position]
    change (((native.imported.data.columns[(0 : Nat)]).get? (offset + index.val)).getD 0 : Source.BaseField) = _
    rw [firstColumn index]
    simp only [Verification.setupPairRow, targetOffset, Nat.zero_add]
  · rw [native.generic_cell_value row (⟨1, by omega⟩ : Fin width), sourceOffset, Nat.zero_add,
      position]
    change (((native.imported.data.columns[(1 : Nat)]).get? (offset + index.val)).getD 0 : Source.BaseField) = _
    rw [secondColumn index]
    simp only [Verification.setupPairRow, targetOffset, Nat.zero_add]
    rfl

theorem materialized_triple_contains (native : MaterializedLookupSetup width)
    (data : Setup.TableData targetWidth) (sourceWide : 3 ≤ width) (targetWide : 3 ≤ targetWidth)
    (offset : Nat) (sourceOffset : native.imported.data.offset = 0) (targetOffset : data.offset = 0)
    (row : Fin native.imported.data.length) (index : Fin data.length)
    (position : row.val = offset + index.val)
    (firstColumn : ∀ entry : Fin data.length,
      native.imported.data.columns[(0 : Nat)].get? (offset + entry.val) = data.columns[(0 : Nat)].get? entry.val)
    (secondColumn : ∀ entry : Fin data.length,
      native.imported.data.columns[(1 : Nat)].get? (offset + entry.val) = data.columns[(1 : Nat)].get? entry.val)
    (thirdColumn : ∀ entry : Fin data.length,
      native.imported.data.columns[(2 : Nat)].get? (offset + entry.val) = data.columns[(2 : Nat)].get? entry.val)
    (name : String) (provided : Array (Source.BaseField × Source.BaseField × Source.BaseField)) :
    (Verification.setupTripleTable (p := babyBearModulus) name data targetWide).Contains provided
      (native.value row (.generic 0), native.value row (.generic 1), native.value row (.generic 2)) := by
  change ∃ entry : Fin data.length,
    (native.value row (.generic 0), native.value row (.generic 1), native.value row (.generic 2)) =
      (((Verification.setupTripleRow data targetWide entry).1 : Source.BaseField),
        ((Verification.setupTripleRow data targetWide entry).2.1 : Source.BaseField),
        ((Verification.setupTripleRow data targetWide entry).2.2 : Source.BaseField))
  refine ⟨index, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
  · rw [native.generic_cell_value row (⟨0, by omega⟩ : Fin width), sourceOffset, Nat.zero_add,
      position]
    change (((native.imported.data.columns[(0 : Nat)]).get? (offset + index.val)).getD 0 : Source.BaseField) = _
    rw [firstColumn index]
    simp only [Verification.setupTripleRow, targetOffset, Nat.zero_add]
  · rw [native.generic_cell_value row (⟨1, by omega⟩ : Fin width), sourceOffset, Nat.zero_add,
      position]
    change (((native.imported.data.columns[(1 : Nat)]).get? (offset + index.val)).getD 0 : Source.BaseField) = _
    rw [secondColumn index]
    simp only [Verification.setupTripleRow, targetOffset, Nat.zero_add]
  · rw [native.generic_cell_value row (⟨2, by omega⟩ : Fin width), sourceOffset, Nat.zero_add,
      position]
    change (((native.imported.data.columns[(2 : Nat)]).get? (offset + index.val)).getD 0 : Source.BaseField) = _
    rw [thirdColumn index]
    simp only [Verification.setupTripleRow, targetOffset, Nat.zero_add]
    rfl

end Airbender.Compiler

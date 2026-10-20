import Airbender.Review.Helpers.Tables.NativeBinaryData
import Airbender.Review.Helpers.Tables.NativeSubwordOffsetData
import Airbender.Review.Helpers.Tables.NativeSubwordLoadData
import Airbender.Review.Helpers.Tables.NativeSubwordStoreClearData
import Airbender.Review.Helpers.Tables.NativeSubwordStorePlaceData
import Airbender.Review.Helpers.Tables.AlignedWordROM

namespace Airbender.Verification.NativeSubwordLookup
set_option autoImplicit false

/-- All seven native regions in compiled offset order. Program-independent
    regions read certified literal data; separator and word-indexed ROM use the
    public image model. General native export/compiler/argument binding remains
    the separate Import boundary. No additional disabled row is inserted. -/
def rowNat (rom : WordROM) (i : Fin 9502721) : Vector Nat 4 :=
  if h : i.val < 1 then NativeBinary.dataZero.rowNat ⟨i.val, by change i.val < 1; omega⟩ else
  if h : i.val < 65537 then (romSeparatorRow ⟨i.val - 1, by omega⟩).push 23 else
  if h : i.val < 2162689 then NativeSubwordOffset.data.rowNat ⟨i.val - 65537, by change i.val - 65537 < 2097152; omega⟩ else
  if h : i.val < 4259841 then NativeSubwordLoad.data.rowNat ⟨i.val - 2162689, by change i.val - 2162689 < 2097152; omega⟩ else
  if h : i.val < 5308417 then (rom.alignedRow ⟨i.val - 4259841, by omega⟩).push 46 else
  if h : i.val < 7405569 then NativeSubwordStoreClear.data.rowNat ⟨i.val - 5308417, by change i.val - 5308417 < 2097152; omega⟩ else
  NativeSubwordStorePlace.data.rowNat ⟨i.val - 7405569, by change i.val - 7405569 < 2097152; omega⟩

/-- The original Clean static table keeps every native value and its table tag.
    Both dynamic slots use this same complete table, as in the native layout. -/
def table {p : Nat} [Fact p.Prime] (rom : WordROM) : Table (ZMod p) (fields 4) := .fromStatic {
  name := "Airbender.V2SubwordMemoryTagged"
  length := 9502721
  row i := (rowNat rom i).map Nat.cast
  index query :=
    let id := query[3].val
    let key := query[0].val
    if id == 0 then 0 else if id == 23 then 1 + key
    else if id == 44 then 65537 + key else if id == 45 then 2162689 + key
    else if id == 46 then 4259841 + key else if id == 54 then 5308417 + key
    else if id == 55 then 7405569 + key else 0
  Spec query := ∃ i, query = (rowNat rom i).map Nat.cast
  contains_iff _ := Iff.rfl
}

/-- The physical selector is the evaluated fourth query field. -/
def lookup {p : Nat} [Fact p.Prime] (rom : WordROM)
    (entry : Vector (Expression (ZMod p)) 3) (selector : Expression (ZMod p)) : Lookup (ZMod p) where
  table := (table rom).toRaw
  entry := entry.push selector

end Airbender.Verification.NativeSubwordLookup

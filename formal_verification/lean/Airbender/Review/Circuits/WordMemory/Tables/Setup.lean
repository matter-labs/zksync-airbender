import Airbender.Review.Circuits.WordMemory.Tables.ZeroData
import Airbender.Review.Circuits.WordMemory.Tables.ROMData

namespace Airbender.Trace.ROM
open Verification

/-- Actual native disabled and ROM regions. All physical values are imported;
    the public program/state binding is a separate specification condition. -/
def importedRow (index : Fin (nativeWordZeroData.length + nativeWordData.length)) : Vector Int 9 :=
  if small : index.val < nativeWordZeroData.length then
    nativeWordZeroData.row ⟨index.val, small⟩
  else nativeWordData.row ⟨index.val - nativeWordZeroData.length, by have := index.isLt; omega⟩

def importedTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.ImportedWordROM"
  length := nativeWordZeroData.length + nativeWordData.length
  row index := (importedRow index).map (fun n : Int => (n : ZMod p))
  index query := if query[8].val = nativeWordDataRegion.id then
      nativeWordZeroData.length + query[0].val / 4 else 0
  Spec query := ∃ index : Fin (nativeWordZeroData.length + nativeWordData.length),
    query = (importedRow index).map (fun n : Int => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Trace.ROM

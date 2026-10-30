import Airbender.Data.Setup.Keccak.ColumnParityIota
import Airbender.Data.Setup.Keccak.ColumnParityControl
import Airbender.Data.Setup.Keccak.ColumnParityXor5

namespace Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 65536

/-- The complete physical native setup domain, including zero padding. -/
def columnParityGenericLength : Nat := 4194304

/-- Dispatch actual retained native rows at their exported offsets. -/
def columnParityGenericRow (index : Fin columnParityGenericLength) : Vector Int 8 :=
  if first : index.val < 65536 then
    columnParityIota.row ⟨index.val, first⟩
  else if second : index.val < 65658 then
    columnParitySlots.row ⟨index.val - 65536, by change index.val - 65536 < 122; omega⟩
  else if third : index.val < 65780 then
    columnParityControl.row ⟨index.val - 65658, by change index.val - 65658 < 122; omega⟩
  else if fourth : index.val < 1114356 then
    (columnParityXor5.row ⟨index.val - 65780, by change index.val - 65780 < 1048576; omega⟩).map Setup.signedValue
  else Vector.replicate 8 0

def columnParityGenericTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 8) := .fromStatic {
  name := "Airbender.SplitColumnParityGeneric"
  length := columnParityGenericLength
  row index := (columnParityGenericRow index).map (fun value : Int => (value : ZMod p))
  index _ := 0
  Spec entry := ∃ index : Fin columnParityGenericLength,
    entry = (columnParityGenericRow index).map (fun value : Int => (value : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Keccak.Split.Native.Fixed

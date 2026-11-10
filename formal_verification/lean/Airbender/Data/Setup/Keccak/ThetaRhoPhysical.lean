import Airbender.Data.Setup.Keccak.ThetaRhoXor
import Airbender.Data.Setup.Keccak.ThetaRhoXorSplit
import Airbender.Data.Setup.Keccak.SplitControl
import Airbender.Data.Setup.Keccak.ThetaRhoSlots

namespace Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 65536

/-- The complete physical native setup domain, including zero padding. -/
def thetaRhoPhysicalGenericLength : Nat := 4194304

/-- Dispatch actual retained native rows at their exported offsets. -/
def thetaRhoPhysicalGenericRow (index : Fin thetaRhoPhysicalGenericLength) : Vector Int 9 :=
  if first : index.val < 65536 then
    (thetaRhoXor.row ⟨index.val, first⟩).map Setup.signedValue
  else if second : index.val < 589824 then
    (thetaRhoXorSplit.row ⟨index.val - 65536, by change index.val - 65536 < 524288; omega⟩).map Setup.signedValue
  else if third : index.val < 589945 then
    thetaRhoControl.row ⟨index.val - 589824, by change index.val - 589824 < 121; omega⟩
  else if fourth : index.val < 590066 then
    thetaRhoSlots.row ⟨index.val - 589945, by change index.val - 589945 < 121; omega⟩
  else Vector.replicate 9 0

def thetaRhoPhysicalGenericTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.SplitThetaRhoPhysical"
  length := thetaRhoPhysicalGenericLength
  row index := (thetaRhoPhysicalGenericRow index).map (fun value : Int => (value : ZMod p))
  index _ := 0
  Spec entry := ∃ index : Fin thetaRhoPhysicalGenericLength,
    entry = (thetaRhoPhysicalGenericRow index).map (fun value : Int => (value : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Keccak.Split.Native.Fixed

import Airbender.Review.Circuits.Blake2G.Tables.ControllerData
import Airbender.Review.Circuits.Blake2G.Tables.XorData
import Airbender.Review.Helpers.Tables.Range

namespace Airbender.Blake2G

/- The generalized table retains arbitrary controller outputs. Its five fixed
   regions are literal imports; XOR semantics is proved from those data. -/

/-- Actual fixed rows with the original arbitrary-controller interface. -/
def setupRow (control : Fin 512 → Vector Nat 7) (index : Fin 344896) : Vector Nat 9 :=
  let n := index.val
  if n < xor8DataRegion.offset + xor8DataRegion.length then xorRegionRow 0 n
  else if n < xor3DataRegion.offset + xor3DataRegion.length then
    xorRegionRow 1 (n - xor3DataRegion.offset)
  else if n < xor4DataRegion.offset + xor4DataRegion.length then
    xorRegionRow 2 (n - xor4DataRegion.offset)
  else if n < xor7DataRegion.offset + xor7DataRegion.length then
    xorRegionRow 3 (n - xor7DataRegion.offset)
  else if h : n < controllerDataRegion.offset then xorRegionRow 4 (n - xor9DataRegion.offset)
  else
    let outputs := control ⟨n - controllerDataRegion.offset, by
      have bound := index.isLt
      have lower : ¬n < 344384 := h
      dsimp [n] at *
      change index.val - 344384 < 512
      omega⟩
    #v[n - controllerDataRegion.offset, outputs[0], outputs[1], outputs[2], outputs[3],
      outputs[4], outputs[5], outputs[6], 28]

def setupTable {p : Nat} [Fact p.Prime] (control : Fin 512 → Vector Nat 7) :
    Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.Blake2G"
  length := 344896
  row i := (setupRow control i).map (fun (n : Nat) => (n : ZMod p))
  index x := match x[8].val with
    | 4 => xor8DataRegion.offset + x[0].val * 256 + x[1].val
    | 17 => xor3DataRegion.offset + x[0].val * 8 + x[1].val
    | 18 => xor4DataRegion.offset + x[0].val * 16 + x[1].val
    | 19 => xor7DataRegion.offset + x[0].val * 128 + x[1].val
    | 20 => xor9DataRegion.offset + x[0].val * 512 + x[1].val
    | 28 => controllerDataRegion.offset + x[0].val
    | _ => 0
  Spec x := ∃ i : Fin 344896, x = (setupRow control i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Blake2G

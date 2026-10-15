import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Review.Circuits.Blake2Round.Tables.XorData

namespace Airbender.Blake2Round

/-- Four physical columns from this circuit's own exported fixed regions. -/
def setupRow (i : Fin 344384) : Vector Nat 4 :=
  let n := i.val
  if n < xor8DataRegion.offset + xor8DataRegion.length then xorRegionRow 0 n
  else if n < xor3DataRegion.offset + xor3DataRegion.length then
    xorRegionRow 1 (n - xor3DataRegion.offset)
  else if n < xor4DataRegion.offset + xor4DataRegion.length then
    xorRegionRow 2 (n - xor4DataRegion.offset)
  else if n < xor7DataRegion.offset + xor7DataRegion.length then
    xorRegionRow 3 (n - xor7DataRegion.offset)
  else xorRegionRow 4 (n - xor9DataRegion.offset)

def setupTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 4) := .fromStatic {
  name := "Airbender.Blake2Round"
  length := 344384
  row i := (setupRow i).map (fun (n : Nat) => (n : ZMod p))
  index x := match x[3].val with
    | 4 => xor8DataRegion.offset + x[0].val * 256 + x[1].val
    | 17 => xor3DataRegion.offset + x[0].val * 8 + x[1].val
    | 18 => xor4DataRegion.offset + x[0].val * 16 + x[1].val
    | 19 => xor7DataRegion.offset + x[0].val * 128 + x[1].val
    | 20 => xor9DataRegion.offset + x[0].val * 512 + x[1].val
    | _ => 0
  Spec x := ∃ i : Fin 344384, x = (setupRow i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Blake2Round

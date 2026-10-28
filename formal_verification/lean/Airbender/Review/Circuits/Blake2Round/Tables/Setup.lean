import Airbender.Data.Setup.Blake2Round.XorData

namespace Airbender.Blake2Round

/-- All six physical columns from this circuit's own exported fixed regions. -/
def setupRow (i : Fin 606208) : Vector Nat 6 :=
  let n := i.val
  if n < xor8DataRegion.offset + xor8DataRegion.length then xorRegionRow 0 n
  else if n < xor7DataRegion.offset + xor7DataRegion.length then
    xorRegionRow 1 (n - xor7DataRegion.offset)
  else if n < xor9DataRegion.offset + xor9DataRegion.length then
    xorRegionRow 2 (n - xor9DataRegion.offset)
  else if n < xor8CarryDataRegion.offset + xor8CarryDataRegion.length then
    xorRegionRow 3 (n - xor8CarryDataRegion.offset)
  else if n < xor7CarryDataRegion.offset + xor7CarryDataRegion.length then
    xorRegionRow 4 (n - xor7CarryDataRegion.offset)
  else xorRegionRow 5 (n - xor4x3DataRegion.offset)

def setupTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 6) := .fromStatic {
  name := "Airbender.Blake2Round"
  length := 606208
  row i := (setupRow i).map (fun (n : Nat) => (n : ZMod p))
  index x := match x[5].val with
    | 4 => xor8DataRegion.offset + x[0].val * 256 + x[1].val
    | 19 => xor7DataRegion.offset + x[0].val * 128 + x[1].val
    | 20 => xor9DataRegion.offset + x[0].val * 512 + x[1].val
    | 55 => xor8CarryDataRegion.offset + x[2].val * 65536 + x[0].val * 256 + x[1].val
    | 56 => xor7CarryDataRegion.offset + x[2].val * 16384 + x[0].val * 128 + x[1].val
    | 57 => xor4x3DataRegion.offset + x[0].val * 1024 + x[1].val * 128 + x[2].val * 8 + x[3].val
    | _ => 0
  Spec x := ∃ i : Fin 606208, x = (setupRow i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Blake2Round

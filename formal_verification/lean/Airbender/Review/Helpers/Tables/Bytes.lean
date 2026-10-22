import Airbender.Review.Helpers.Tables.Lookups
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Verification

/-- Actual fixed setup rows, selected with their exported native offsets. -/
def shiftBinopRow (index : Fin 524545) : Vector Nat 10 :=
  let n := index.val
  if n < byteSignDataRegion.offset then shiftRegionRow 0 n
  else if n < byteXorDataRegion.offset then shiftRegionRow 1 (n - byteSignDataRegion.offset)
  else if n < byteOrDataRegion.offset then shiftRegionRow 2 (n - byteXorDataRegion.offset)
  else if n < byteAndDataRegion.offset then shiftRegionRow 3 (n - byteOrDataRegion.offset)
  else if n < byteTruncateDataRegion.offset then shiftRegionRow 4 (n - byteAndDataRegion.offset)
  else if n < byteShiftDataRegion.offset then shiftRegionRow 5 (n - byteTruncateDataRegion.offset)
  else shiftRegionRow 6 (n - byteShiftDataRegion.offset)

/-- Clean adapter over the imported setup rows assembled by `shiftBinopRow`.
    `row` casts those natural-number entries into the selected field; `name`
    identifies the table, and `index` is a lookup hint using the native region
    offsets. `Spec` is membership in the actual imported rows, with its checked
    arithmetic semantics supplied by the supporting table proofs. -/
def shiftBinopTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 10) := .fromStatic {
  name := "Airbender.ShiftBinop"
  length := 524545
  row i := (shiftBinopRow i).map (fun (n : Nat) => (n : ZMod p))
  index x := match x[9].val with
    | 3 => byteSignDataRegion.offset + x[0].val
    | 4 => byteXorDataRegion.offset + x[0].val * 256 + x[1].val
    | 6 => byteOrDataRegion.offset + x[0].val * 256 + x[1].val
    | 7 => byteAndDataRegion.offset + x[0].val * 256 + x[1].val
    | 8 => byteTruncateDataRegion.offset + x[0].val * 256 + x[1].val
    | 9 => byteShiftDataRegion.offset + x[0].val * 65536 + x[1].val * 256 + x[2].val * 8 + x[3].val
    | _ => 0
  Spec x := ∃ i : Fin 524545, x = (shiftBinopRow i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

def shiftBinopLookup {p : Nat} [Fact p.Prime] (entry : Vector (Expression (ZMod p)) 10) :
    Lookup (ZMod p) where
  table := shiftBinopTable.toRaw
  entry := entry

end Airbender.Verification

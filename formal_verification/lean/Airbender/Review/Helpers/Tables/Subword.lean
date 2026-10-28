import Airbender.Data.Tables.SubwordROMData
import Airbender.Data.Tables.SubwordData
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control

namespace Airbender.Verification

/-- The generalized public-program interface reads load outputs from the actual
    imported fixed regions. Native selected-program ROM correspondence is proved
    separately; arbitrary public program functions retain their scope. -/
def subwordImportedLimbs (byte : Bool) (key : Nat) : Nat × Nat :=
  let data := if byte then loadByteData else loadHalfData
  let index := key % data.length
  (((data.columns[1]).get? index).getD 0, ((data.columns[2]).get? index).getD 0)

/-- Generalized public-program interface over the imported ROM address layout
    and imported fixed load outputs. The concrete selected-program connection to
    the independently imported ROM output columns is proved separately. -/
def subwordProgramROMRow (program : Nat → BitVec 32) (byte : Bool) (n : Nat) : Vector Nat 9 :=
  let group := if byte then 8 else 4
  let signed := n / (group / 2) % 2
  let highHalf := if byte then n / 2 % 2 else n % 2
  let highByte := if byte then n % 2 else 0
  let half := (program (n / group)).toNat / (if highHalf = 1 then 65536 else 1) % 65536
  let outputs := subwordImportedLimbs byte (half + 65536 * signed + 131072 * highByte)
  ((subwordROMRow byte n).set 1 outputs.1).set 2 outputs.2

/-- Native fixed rows and the original arbitrary-public-program interface. -/
def subwordNativeRow (program : Nat → BitVec 32) (index : Fin 13238273) : Vector Nat 9 :=
  let n := index.val
  if n = subwordZeroDataRegion.offset then
    subwordZeroData.columns.map (fun column => (column.get? 0).getD 0)
  else if n < storeClearDataRegion.offset then subwordFixedRow 0 (n - storePlaceDataRegion.offset)
  else if n < loadHalfDataRegion.offset then subwordFixedRow 1 (n - storeClearDataRegion.offset)
  else if n < loadByteDataRegion.offset then subwordFixedRow 2 (n - loadHalfDataRegion.offset)
  else if n < subwordROMHalfDataRegion.offset then subwordFixedRow 3 (n - loadByteDataRegion.offset)
  else if n < subwordROMByteDataRegion.offset then
    subwordProgramROMRow program false (n - subwordROMHalfDataRegion.offset)
  else subwordProgramROMRow program true (n - subwordROMByteDataRegion.offset)

def subwordTableOfRows {p : Nat} [Fact p.Prime] (rows : Fin 13238273 → Vector Nat 9) :
    Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.SubwordMemory"
  length := 13238273
  row i := (rows i).map (fun (n : Nat) => (n : ZMod p))
  index x :=
    if x[8].val = storePlaceDataRegion.id then storePlaceDataRegion.offset + x[0].val
    else if x[8].val = storeClearDataRegion.id then storeClearDataRegion.offset + x[0].val
    else if x[8].val = loadHalfDataRegion.id then loadHalfDataRegion.offset + x[0].val
    else if x[8].val = loadByteDataRegion.id then loadByteDataRegion.offset + x[0].val
    else if x[8].val = subwordROMHalfDataRegion.id then
      subwordROMHalfDataRegion.offset + 4 * (x[0].val % 4194304 / 4) +
        2 * (x[0].val / 4194304 % 2) + x[0].val / 8388608 % 2
    else if x[8].val = subwordROMByteDataRegion.id then
      subwordROMByteDataRegion.offset + 8 * (x[0].val % 4194304 / 4) +
        4 * (x[0].val / 4194304 % 2) + 2 * (x[0].val / 8388608 % 2) +
        x[0].val / 16777216 % 2
    else subwordZeroDataRegion.offset
  Spec x := ∃ i : Fin 13238273, x = (rows i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

/-- General public-program specialization of the imported fixed-row view. -/
def subwordTable {p : Nat} [Fact p.Prime] (program : Nat → BitVec 32) :
    Table (ZMod p) (fields 9) := subwordTableOfRows (subwordNativeRow program)

/-- Complete native row view, including both independently imported ROM regions. -/
def importedSubwordRow (index : Fin 13238273) : Vector Nat 9 :=
  if index.val < subwordROMHalfDataRegion.offset then subwordNativeRow (fun _ => 0) index
  else if index.val < subwordROMByteDataRegion.offset then
    subwordROMRow false (index.val - subwordROMHalfDataRegion.offset)
  else subwordROMRow true (index.val - subwordROMByteDataRegion.offset)

def importedSubwordTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 9) :=
  subwordTableOfRows importedSubwordRow

end Airbender.Verification

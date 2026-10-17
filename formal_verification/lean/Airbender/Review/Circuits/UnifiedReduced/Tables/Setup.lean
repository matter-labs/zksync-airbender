import Airbender.Review.Helpers.Tables.Bytes
import Airbender.Review.Helpers.Memory.ROM
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.UnifiedReduced.Setup
open Verification Trace

/-- Compatibility map between ordinary and native wide-binop discriminators. -/
def binaryTag (tag : Nat) : Nat :=
  if tag = 4 then 52 else if tag = 6 then 53 else if tag = 7 then 54 else tag

/-- Logical enumeration of imported regions. Native physical offsets remain
    in nativeFixedRegion; lengths and discriminators come from those artifacts. -/
def logicalFixedOffset (kind : Nat) : Nat :=
  ((List.finRange 15).take kind).foldl (fun total i => total + (nativeFixedData i).length) 0

/-- The existing binary interface projects actual unified regions. -/
def binaryRow (index : Fin 524545) : Vector Nat 10 :=
  let n := index.val
  if n < logicalFixedOffset 1 then nativeFixedRow 0 n
  else if n < logicalFixedOffset 2 then nativeFixedRow 1 (n - logicalFixedOffset 1)
  else if n < logicalFixedOffset 3 then nativeFixedRow 2 (n - logicalFixedOffset 2)
  else if n < logicalFixedOffset 4 then nativeFixedRow 3 (n - logicalFixedOffset 3)
  else if n < logicalFixedOffset 5 then nativeFixedRow 4 (n - logicalFixedOffset 4)
  else if n < logicalFixedOffset 6 then nativeFixedRow 5 (n - logicalFixedOffset 5)
  else nativeFixedRow 6 (n - logicalFixedOffset 6)

/-- Four native XOR-rotate regions, retaining their exported outputs. -/
def rotateRow (index : Fin 262144) : Vector Nat 10 :=
  nativeFixedRow ⟨11 + index.val / 65536, by have := index.isLt; omega⟩ (index.val % 65536)

/-- Logical membership view of all actual imported fixed regions. -/
def fixedRow (index : Fin 1048961) : Vector Nat 10 :=
  let n := index.val
  if h : n < logicalFixedOffset 7 then binaryRow ⟨n, by
    change n < 524545 at h; exact h⟩
  else if n < logicalFixedOffset 8 then nativeFixedRow 7 (n - logicalFixedOffset 7)
  else if n < logicalFixedOffset 9 then nativeFixedRow 8 (n - logicalFixedOffset 8)
  else if n < logicalFixedOffset 10 then nativeFixedRow 9 (n - logicalFixedOffset 9)
  else if n < logicalFixedOffset 11 then nativeFixedRow 10 (n - logicalFixedOffset 10)
  else rotateRow ⟨n - logicalFixedOffset 11, by
    have size := index.isLt
    change n - 786817 < 262144
    omega⟩

/-- Preserve the arbitrary public-program interface; selected-program native
    ROM contents are connected to this view separately from the fixed regions. -/
def row (before : Reference.RiscV.Sail.State) (index : Fin 2097537) : Vector Nat 10 :=
  if h : index.val < 1048961 then fixedRow ⟨index.val, h⟩ else
    let key := index.val - 1048961
    let word := Arithmetic.Word.ofBitVec (ROM.words before key)
    #v[4 * key, word.lo, word.hi, 0, 0, 0, 0, 0, 0, 34]

/-- One concrete Clean static table for the pooled unified queries. The public
    initial state fixes ROM contents; the witness supplies no table values.
    The imported selected-program specialization is connected to this generalized
    public-program interface by a kernel-checked image-binding theorem. -/
def tableOfRows {p : Nat} [Fact p.Prime] (rows : Fin 2097537 → Vector Nat 10) :
    Table (ZMod p) (fields 10) := .fromStatic {
  name := "Airbender.UnifiedReduced"
  length := 2097537
  row i := (rows i).map (fun (n : Nat) => (n : ZMod p))
  index query :=
    match (List.finRange 15).find? (fun kind => (nativeFixedRegion kind).id == query[9].val) with
    | some kind =>
      let key := if kind.val = 0 then 0
        else if kind.val = 1 ∨ kind.val = 7 ∨ kind.val = 8 ∨ kind.val = 9 ∨ kind.val = 10
          then query[0].val
        else if kind.val = 6 then query[0].val * 65536 + query[1].val * 256 +
          query[2].val * 8 + query[3].val
        else query[0].val * 256 + query[1].val
      logicalFixedOffset kind.val + key
    | none => if query[9].val = 34 then logicalFixedOffset 15 + query[0].val / 4 else 0
  Spec query := ∃ i : Fin 2097537, query = (rows i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

def table {p : Nat} [Fact p.Prime] (before : Reference.RiscV.Sail.State) :
    Table (ZMod p) (fields 10) := tableOfRows (row before)

/-- The complete selected-program native table view. Logical enumeration may
    reorder native regions; every cell is read from its exported region. -/
def importedRow (index : Fin 2097537) : Vector Nat 10 :=
  if h : index.val < 1048961 then fixedRow ⟨index.val, h⟩ else
    nativeROMData.columns.map (fun column => (column.get? (index.val - 1048961)).getD 0)

def importedTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 10) :=
  tableOfRows importedRow

end Airbender.UnifiedReduced.Setup

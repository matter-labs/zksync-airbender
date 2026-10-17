import Airbender.Review.Circuits.UnifiedReduced.Tables.Setup
import Airbender.Proofs.Tables.ReferenceControl

namespace Airbender.UnifiedReduced.Setup
open Verification Trace

def referenceBinaryRow (index : Fin 524545) : Vector Nat 10 :=
  (shiftBinopRow index).set 9 (binaryTag (shiftBinopRow index)[9])

/-- Pack the unified seven-bit conditional key into the already modeled
    standalone key. Only the second operand's sign is needed, rather than its
    entire high limb. Both tables use the same conditional-resolution function. -/
def conditionalKey (key : Nat) : Nat :=
  key % 2 * 32768 + (key / 2 % 2) * 65536 + (key / 4 % 2) * 131072 +
    (key / 8 % 2) * 262144 + (key / 16 % 8) * 524288

/-- Native XOR-rotate rows from `cs/src/tables/binops.rs`: two byte inputs
    produce four bytes of the rotated contribution. This is table data;
    instruction behavior continues to use the existing project/Sail references. -/
def referenceRotateRow (index : Fin 262144) : Vector Nat 10 :=
  let rotation := #[16, 12, 8, 7][index.val / 65536]!
  let a := index.val / 256 % 256
  let b := index.val % 256
  let out := (BitVec.ofNat 32 (a ^^^ b)).rotateRight rotation
  #v[a, b, out.toNat % 256, out.toNat / 256 % 256,
    out.toNat / 65536 % 256, out.toNat / 16777216 % 256,
    0, 0, 0, 47 + index.val / 65536]

/-- All fixed unified setup rows: shifts/wide binops, zero tests, limb signs,
    jump cleanup, seven-bit conditional resolution and XOR-rotate. Region
    lengths and IDs follow `unified_reduced_machine/circuit.rs` and
    `definitions/table_type.rs`. Rows are modeled, not extracted. -/
def referenceFixedRow (index : Fin 1048961) : Vector Nat 10 :=
  let n := index.val
  if h : n < 524545 then referenceBinaryRow ⟨n, h⟩
  else if n < 655617 then
    let key := n - 524545
    #v[key, if key = 0 then 1 else 0, 0, 0, 0, 0, 0, 0, 0, 1]
  else if n < 721153 then
    let key := n - 655617
    #v[key, key / 32768, 0, 0, 0, 0, 0, 0, 0, 5]
  else if n < 786689 then
    let key := n - 721153
    #v[key, key / 2 % 2, key - key % 4, 0, 0, 0, 0, 0, 0, 2]
  else if n < 786817 then
    let key := n - 786689
    #v[key, conditionalValue (conditionalKey key), 0, 0, 0, 0, 0, 0, 0, 51]
  else referenceRotateRow ⟨n - 786817, by have := index.isLt; dsimp [n] at *; omega⟩

/-- Fixed setup plus aligned ROM words read from the public Sail byte image.
    Missing words pad with zero, as in the existing modeled ROM interface;
    successful access/public-image conditions remain visible in the trace model.
    Column 9 holds the table ID; unused columns are zero. -/
def referenceRow (before : Reference.RiscV.Sail.State) (index : Fin 2097537) : Vector Nat 10 :=
  if h : index.val < 1048961 then referenceFixedRow ⟨index.val, h⟩ else
    let key := index.val - 1048961
    let word := Arithmetic.Word.ofBitVec (ROM.words before key)
    #v[4 * key, word.lo, word.hi, 0, 0, 0, 0, 0, 0, 34]


end Airbender.UnifiedReduced.Setup

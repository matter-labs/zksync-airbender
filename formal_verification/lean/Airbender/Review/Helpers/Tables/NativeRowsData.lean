import Airbender.Review.Helpers.Tables.NativeScalarData
import Airbender.Review.Helpers.Tables.NativeDecoderData

namespace Airbender.Verification.NativeSetup

/-- The actual compiled setup layout selected by each certified native prefix. -/
abbrev DecoderKind.columns : DecoderKind → SetupColumns
  | .arithmetic => AddSub.importedConstraintsSetupColumns
  | .wordMemory | .wordMemoryHoles => WordMemory.importedConstraintsSetupColumns

/-- Row widths; the proof layer checks equality with the imported descriptor. -/
abbrev DecoderKind.width : DecoderKind → Nat
  | .arithmetic => 12
  | .wordMemory | .wordMemoryHoles => 16

/-- Native arithmetic setup has only the two scalar columns and decoder group. -/
def arithmeticRow (row : Row) : Vector (ZMod mersenne31Modulus) 12 :=
  Vector.ofFn fun column =>
    if column.val = 0 then scalarRow .range16 row
    else if column.val = 1 then scalarRow .timestamp19 row
    else (decoderRow .arithmetic row)[column.val - 2]'(by have := column.isLt; omega)

/-- Native memory setup inserts the complete tagged group before the decoder. -/
def memoryRow (kind : DecoderKind) (rom : WordROM) (row : Row) :
    Vector (ZMod mersenne31Modulus) 16 :=
  Vector.ofFn fun column =>
    if column.val = 0 then scalarRow .range16 row
    else if column.val = 1 then scalarRow .timestamp19 row
    else if generic : column.val < 6 then
      (genericRow (p := mersenne31Modulus) rom row)[column.val - 2]'(by omega)
    else (decoderRow kind row)[column.val - 6]'(by have := column.isLt; omega)

/-- Complete source-shaped active rows. Scalar zero fill, tagged generic tuples
    and decoder sentinels coexist. Row excludes final normalization; this is not
    Rust/LDE refinement. Equality with imported placement is checked in Proofs. -/
def activeRow (kind : DecoderKind) (rom : WordROM) (row : Row) :
    Vector (ZMod mersenne31Modulus) kind.width :=
  match kind with
  | .arithmetic => arithmeticRow row
  | .wordMemory => memoryRow .wordMemory rom row
  | .wordMemoryHoles => memoryRow .wordMemoryHoles rom row

/-- A contiguous query observes actual columns, and fails if its full width
    does not fit. No out-of-bounds value is replaced with zero. -/
def window (kind : DecoderKind) (rom : WordROM) (row : Row) (start size : Nat) :
    Option (Vector (ZMod mersenne31Modulus) size) :=
  if bound : start + size ≤ kind.width then
    some (Vector.ofFn fun i => (activeRow kind rom row)[start + i.val])
  else none

def ColumnLookup (kind : DecoderKind) (rom : WordROM) (start : Nat)
    {size : Nat} (query : Vector (ZMod mersenne31Modulus) size) : Prop :=
  ∃ row : Row, window kind rom row start size = some query

/-- Scalar positions are taken from the imported compiled descriptor. -/
def scalarColumn (kind : DecoderKind) : ScalarKind → Nat
  | .range16 => kind.columns.range16
  | .timestamp19 => kind.columns.timestamp19

/-- A complete native generic tuple includes its table tag. The arithmetic
    layout has no generic group, so it cannot authenticate a tagged lookup. -/
def TaggedLookup (kind : DecoderKind) (rom : WordROM) (tag : Nat)
    (query : Vector (ZMod mersenne31Modulus) 3) : Prop :=
  kind.columns.genericGroups = 1 ∧ ColumnLookup kind rom kind.columns.genericStart (query.push tag)

end Airbender.Verification.NativeSetup

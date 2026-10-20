import Airbender.Review.Circuits.ShiftBinop.Tables.NativeCsrData
import Airbender.Review.Helpers.Tables.NativeBinaryData
import Airbender.Review.Helpers.Tables.NativeShiftScalarData
import Airbender.Review.Helpers.Tables.NativeSllLowData
import Airbender.Review.Helpers.Tables.NativeSllHighData
import Airbender.Review.Helpers.Tables.NativeSrlLowData
import Airbender.Review.Helpers.Tables.NativeSrlHighData
import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification.NativeShiftLookup

/-- All native tagged rows, in compiled offset order, without a new disabled row.
    Each branch reads literal native columns, including the compilation fixture’s CSR-properties region.
    Parser/emitter/compiler refinement remains the separate Import boundary. -/
def rowNat (i : Fin 10817537) : Vector Nat 4 :=
  if h : i.val < 1 then NativeBinary.dataZero.rowNat ⟨i.val - 0, by change i.val - 0 < 1; omega⟩ else
  if h : i.val < 65537 then NativeBinary.dataXor.rowNat ⟨i.val - 1, by change i.val - 1 < 65536; omega⟩ else
  if h : i.val < 131073 then NativeBinary.dataOr.rowNat ⟨i.val - 65537, by change i.val - 65537 < 65536; omega⟩ else
  if h : i.val < 196609 then NativeBinary.dataAnd.rowNat ⟨i.val - 131073, by change i.val - 131073 < 65536; omega⟩ else
  if h : i.val < 200705 then NativeShiftCsr.data.rowNat ⟨i.val - 196609, by change i.val - 196609 < 4096; omega⟩ else
  if h : i.val < 266241 then NativeShiftScalars.dataTruncate.rowNat ⟨i.val - 200705, by change i.val - 200705 < 65536; omega⟩ else
  if h : i.val < 2363393 then NativeSllLow.data.rowNat ⟨i.val - 266241, by change i.val - 266241 < 2097152; omega⟩ else
  if h : i.val < 4460545 then NativeSllHigh.data.rowNat ⟨i.val - 2363393, by change i.val - 2363393 < 2097152; omega⟩ else
  if h : i.val < 6557697 then NativeSrlLow.data.rowNat ⟨i.val - 4460545, by change i.val - 4460545 < 2097152; omega⟩ else
  if h : i.val < 8654849 then NativeSrlHigh.data.rowNat ⟨i.val - 6557697, by change i.val - 6557697 < 2097152; omega⟩ else
  if h : i.val < 10752001 then NativeShiftScalars.dataSignFill.rowNat ⟨i.val - 8654849, by change i.val - 8654849 < 2097152; omega⟩ else
  NativeShiftScalars.dataRange.rowNat ⟨i.val - 10752001, by change i.val - 10752001 < 65536; omega⟩

/-- The original Clean static table retains all four native fields. Its CSR region
    is the exact compilation fixture; binding runtime CSR setup is separate. -/
def table {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 4) := .fromStatic {
  name := "Airbender.V2ShiftBinopCompilationTagged"
  length := 10817537
  row i := (rowNat i).map Nat.cast
  index query :=
    let id := query[3].val
    let key := query[0].val
    if id == 0 then 0
    else if id == 4 then 1 + key * 256 + query[1].val
    else if id == 6 then 65537 + key * 256 + query[1].val
    else if id == 7 then 131073 + key * 256 + query[1].val
    else if id == 25 then 196609 + key else if id == 47 then 200705 + key
    else if id == 48 then 266241 + key else if id == 49 then 2363393 + key
    else if id == 50 then 4460545 + key else if id == 51 then 6557697 + key
    else if id == 52 then 8654849 + key else if id == 53 then 10752001 + key
    else 0
  Spec query := ∃ i, query = (rowNat i).map Nat.cast
  contains_iff _ := Iff.rfl
}

/-- A native query's table selector is an evaluated fourth expression. -/
def lookup {p : Nat} [Fact p.Prime] (entry : Vector (Expression (ZMod p)) 3)
    (selector : Expression (ZMod p)) : Lookup (ZMod p) where
  table := (table (p := p)).toRaw
  entry := entry.push selector

end Airbender.Verification.NativeShiftLookup

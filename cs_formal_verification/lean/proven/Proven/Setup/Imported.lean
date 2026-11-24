module
public import Human.Compiler.NativeSetups.Rows
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/- Facts about imported setup data: the generic columns of a row as a list, the virtual range columns, and the
   lookup groups of `importedRows`. -/

namespace Airbender.Import.Setup.Proofs
open Airbender.Import.Setup

/-- The generic columns of row `index`, in native column order, are the row that `Rows` gives. -/
theorem columns_row {data : SetupData} {width : Nat} {rows : Nat → Vector Int width} (h : data.Rows rows)
    {index : Nat} (bound : index < data.traceLen) :
    data.columns.toList.map (decode · index) = (rows index).toList := by
  obtain ⟨size, values⟩ := h
  apply List.ext_getElem
  · simp [size]
  · intro column inside _
    have inside : column < width := by simpa [size] using inside
    have := values index bound ⟨column, inside⟩
    simp only [Array.getD, show column < data.columns.size by omega, ↓reduceDIte] at this
    simpa using this

/-- An increasing prefix of `length` rows, then zero padding. -/
theorem decode_identity_padding (length padding n : Nat) :
    decode [.affine length 0 1, .affine padding 0 0] n = if n < length then (n : Int) else 0 := by
  simp only [decode, Block.len, Block.valueAt]
  split_ifs <;> simp_all

/-- An increasing column of `length` rows. -/
theorem decode_identity (length n : Nat) :
    decode [.affine length 0 1] n = if n < length then (n : Int) else 0 := by
  simp only [decode, Block.len, Block.valueAt]
  split_ifs <;> simp_all

end Airbender.Import.Setup.Proofs

namespace Airbender.Compiler.NativeSetups
open Airbender.Import.Setup Airbender.Import.Setup.Proofs NativeArithmetic

/-- The lookup groups of imported data with the native range columns. -/
theorem importedRows_eq {data : SetupData} (index : Nat)
    (range16 : decode data.range16 index = if index < 65536 then (index : Int) else 0)
    (timestamp : decode data.timestampRange index = if index < 524288 then (index : Int) else 0) (group : Fin 3) :
    importedRows data group index =
      if group.val = 0 then (data.columns.toList.map (decode · index)).map (fun value : Int => (value : F))
      else if group.val = 1 then [if index < 65536 then (index : F) else 0]
      else [if index < 524288 then (index : F) else 0] := by
  unfold importedRows
  split_ifs <;> simp_all

end Airbender.Compiler.NativeSetups

import Airbender.Proofs.Keccak.SplitParityIotaBinding

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

/-- The actual signed native byte-iota row has the exact original field values. -/
theorem column_parity_iota_field_row (index : Fin columnParityIota.length) :
    (columnParityIota.row index).map (fun value : Int => (value : ZMod babyBearModulus)) =
      (Airbender.Keccak.byteRow 38 index.val).map (fun value : Nat => (value : ZMod babyBearModulus)) := by
  have reference := column_parity_iota_reference index.val index.isLt
  have offset : columnParityIota.offset = 0 := by rfl
  apply Vector.ext
  intro column valid
  have values := congrArg (fun row : Vector Nat 8 => (row.map
    (fun value : Nat => (value : ZMod babyBearModulus)))[column]) reference
  simpa only [TableData.row, Vector.getElem_map, signedValue_cast, offset, Nat.zero_add] using values

/-- Native byte-iota membership bounds both byte keys and proves the actual output. -/
theorem column_parity_iota_table_sound [Fact babyBearModulus.Prime]
    (row : Vector (ZMod babyBearModulus) 8)
    (sound : (columnParityIota.table "Airbender.SplitColumnParityIota").toRaw.Soundness #[] row) :
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 256 ∧
      row[2].val = row[0].val ^^^ Airbender.Keccak.iotaByte row[1].val := by
  change ∃ index : Fin columnParityIota.length,
    row = (columnParityIota.row index).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  rw [column_parity_iota_field_row]
  let a := index.val % 256
  let b := index.val / 256
  let c := a ^^^ Airbender.Keccak.iotaByte b
  have input : a < 256 := Nat.mod_lt _ (by decide)
  have control : b < 256 := by have := index.isLt; change index.val < 65536 at this; dsimp [b]; omega
  have constant : Airbender.Keccak.iotaByte b < 256 := Nat.mod_lt _ (by decide)
  have output : c < 256 := Nat.xor_lt_two_pow (n := 8) input constant
  simp only [Vector.getElem_map, Airbender.Keccak.byteRow, ↓reduceIte,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  change (a : ZMod babyBearModulus).val < 256 ∧ (b : ZMod babyBearModulus).val < 256 ∧
    (c : ZMod babyBearModulus).val < 256 ∧ (c : ZMod babyBearModulus).val =
      (a : ZMod babyBearModulus).val ^^^ Airbender.Keccak.iotaByte (b : ZMod babyBearModulus).val
  rw [ZMod.val_natCast_of_lt (lt_trans input (by decide)),
    ZMod.val_natCast_of_lt (lt_trans control (by decide)),
    ZMod.val_natCast_of_lt (lt_trans output (by decide))]
  exact ⟨input, control, output, rfl⟩

end Airbender.Keccak.Split.Native.Fixed.Proofs

import Airbender.Review.Helpers.Tables.Range
import Airbender.Review.Circuits.ReducedMachine.Tables.NativeData

namespace Airbender.ReducedMachine.NativeFixed

/-- Complete actual tagged pool in native offset order, without an added row. -/
def rowNat (i : Fin 5771521) : Vector Nat 4 :=
  if h : i.val < 1 then dataT0.rowNat ⟨i.val - 0, by change i.val - 0 < 1; omega⟩ else
  if h : i.val < 65537 then dataT4.rowNat ⟨i.val - 1, by change i.val - 1 < 65536; omega⟩ else
  if h : i.val < 131073 then dataT6.rowNat ⟨i.val - 65537, by change i.val - 65537 < 65536; omega⟩ else
  if h : i.val < 196609 then dataT7.rowNat ⟨i.val - 131073, by change i.val - 131073 < 65536; omega⟩ else
  if h : i.val < 262145 then dataT16.rowNat ⟨i.val - 196609, by change i.val - 196609 < 65536; omega⟩ else
  if h : i.val < 327681 then dataT17.rowNat ⟨i.val - 262145, by change i.val - 262145 < 65536; omega⟩ else
  if h : i.val < 393217 then dataT18.rowNat ⟨i.val - 327681, by change i.val - 327681 < 65536; omega⟩ else
  if h : i.val < 393345 then dataT20.rowNat ⟨i.val - 393217, by change i.val - 393217 < 128; omega⟩ else
  if h : i.val < 393473 then dataT22.rowNat ⟨i.val - 393345, by change i.val - 393345 < 128; omega⟩ else
  if h : i.val < 459009 then dataT23.rowNat ⟨i.val - 393473, by change i.val - 393473 < 65536; omega⟩ else
  if h : i.val < 1507585 then dataT24.rowNat ⟨i.val - 459009, by change i.val - 459009 < 1048576; omega⟩ else
  if h : i.val < 1511681 then dataT25.rowNat ⟨i.val - 1507585, by change i.val - 1507585 < 4096; omega⟩ else
  if h : i.val < 5705985 then dataT37.rowNat ⟨i.val - 1511681, by change i.val - 1511681 < 4194304; omega⟩ else
  dataT47.rowNat ⟨i.val - 5705985, by change i.val - 5705985 < 65536; omega⟩

/-- The retained public fixture determines the ROM/CSR regions. General public
    configuration and physical setup enforcement remain separate obligations. -/
def table {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 4) := .fromStatic {
  name := "Airbender.V2ReducedNativeTagged"
  length := 5771521
  row i := (rowNat i).map Nat.cast
  index query :=
    let tag := query[3].val
    let key := query[0].val
    if tag == 0 then 0 else
    if tag == 4 then 1 + key * 256 + query[1].val else
    if tag == 6 then 65537 + key * 256 + query[1].val else
    if tag == 7 then 131073 + key * 256 + query[1].val else
    if tag == 16 then 196609 + key else
    if tag == 17 then 262145 + key else
    if tag == 18 then 327681 + key else
    if tag == 20 then 393217 + key else
    if tag == 22 then 393345 + key else
    if tag == 23 then 393473 + key else
    if tag == 24 then 459009 + key / 4 else
    if tag == 25 then 1507585 + key else
    if tag == 37 then 1511681 + key else
    if tag == 47 then 5705985 + key else
    0
  Spec query := ∃ i, query = (rowNat i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.ReducedMachine.NativeFixed

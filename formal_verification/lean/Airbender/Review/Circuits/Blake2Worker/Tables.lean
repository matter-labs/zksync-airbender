import Airbender.Review.Helpers.Tables.Range
import Airbender.Review.Circuits.Blake2Worker.FixedData4
import Airbender.Review.Circuits.Blake2Worker.FixedData26
import Airbender.Review.Circuits.Blake2Worker.FixedData27
import Airbender.Review.Circuits.Blake2Worker.FixedData28
import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Mersenne31

namespace Airbender.Blake2Worker.Fixed

inductive Kind where
  | byte | three | four | seven | nine
  deriving DecidableEq

def Kind.bound : Kind → Nat
  | .byte => 256 | .three => 8 | .four => 16 | .seven => 128 | .nine => 512

def Kind.tag : Kind → Nat
  | .byte => 4 | .three => 26 | .four => 27 | .seven => 28 | .nine => 29

def Kind.offset : Kind → Nat
  | .byte => 0 | .three => 65536 | .four => 65600 | .seven => 65856 | .nine => 82240

def data : Kind → Setup.TableData 4
  | .byte => dataT4 | .three => dataT26 | .four => dataT27 | .seven => dataT28 | .nine => dataT29

/-- Actual stored rows in native pool order, including the returned value. -/
def rowNat (i : Fin 344384) : Vector Nat 4 :=
  if h : i.val < 65536 then dataT4.rowNat ⟨i.val, h⟩ else
  if h : i.val < 65600 then dataT26.rowNat ⟨i.val-65536,by change i.val-65536 < 64; omega⟩ else
  if h : i.val < 65856 then dataT27.rowNat ⟨i.val-65600,by change i.val-65600 < 256; omega⟩ else
  if h : i.val < 82240 then dataT28.rowNat ⟨i.val-65856,by change i.val-65856 < 16384; omega⟩ else
  dataT29.rowNat ⟨i.val-82240,by change i.val-82240 < 262144; omega⟩

/-- Concrete native-shaped complete worker pool. The returned value is always
    imported data; no XOR recipe or table-equivalence premise defines membership. -/
def table {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 4) := .fromStatic {
  name := "Airbender.V2Blake2WorkerNativeFixed"
  length := 344384
  row i := (rowNat i).map Nat.cast
  index query :=
    let tag := query[3].val
    let base := if tag == 4 then 256 else if tag == 26 then 8 else if tag == 27 then 16 else if tag == 28 then 128 else 512
    let offset := if tag == 4 then 0 else if tag == 26 then 65536 else if tag == 27 then 65600 else if tag == 28 then 65856 else 82240
    offset + query[0].val * base + query[1].val
  Spec query := ∃ i, query = (rowNat i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Blake2Worker.Fixed

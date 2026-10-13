import Airbender.Review.Helpers.Tables.Range
import Mathlib.Data.Nat.Bitwise

namespace Airbender.Blake2G

/- XOR rows model cs/src/tables/binops.rs::create_xor_table, with the five
   widths/regions checked by the importer. Rust setup correspondence is deferred.
   The seven control outputs are supplied separately; no control semantics is
   asserted by the mixing proof. -/

def xorRow (width tag index : Nat) : Vector Nat 9 :=
  let a := index / 2 ^ width
  let b := index % 2 ^ width
  #v[a, b, a ^^^ b, 0, 0, 0, 0, 0, tag]

def setupRow (control : Fin 512 → Vector Nat 7) (index : Fin 344896) : Vector Nat 9 :=
  let n := index.val
  if n < 65536 then xorRow 8 4 n
  else if n < 65600 then xorRow 3 17 (n - 65536)
  else if n < 65856 then xorRow 4 18 (n - 65600)
  else if n < 82240 then xorRow 7 19 (n - 65856)
  else if h : n < 344384 then xorRow 9 20 (n - 82240)
  else
    let outputs := control ⟨n - 344384, by have bound := index.isLt; dsimp [n] at *; omega⟩
    #v[n - 344384, outputs[0], outputs[1], outputs[2], outputs[3], outputs[4],
      outputs[5], outputs[6], 28]

def setupTable {p : Nat} [Fact p.Prime] (control : Fin 512 → Vector Nat 7) :
    Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.Blake2G"
  length := 344896
  row i := (setupRow control i).map (fun (n : Nat) => (n : ZMod p))
  index x := match x[8].val with
    | 4 => x[0].val * 256 + x[1].val
    | 17 => 65536 + x[0].val * 8 + x[1].val
    | 18 => 65600 + x[0].val * 16 + x[1].val
    | 19 => 65856 + x[0].val * 128 + x[1].val
    | 20 => 82240 + x[0].val * 512 + x[1].val
    | 28 => 344384 + x[0].val
    | _ => 0
  Spec x := ∃ i : Fin 344896, x = (setupRow control i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Blake2G

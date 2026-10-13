import Airbender.Review.Circuits.Blake2G.Tables.Setup

namespace Airbender.Blake2Round

/-- The same five XOR regions as G, without its controller region or padding
    columns. Both Rust circuits use `tables/binops.rs::create_xor_table`.
    This is a shared modeled setup, not an extracted Rust setup artifact. -/
def setupRow (i : Fin 344384) : Vector Nat 4 :=
  let row := Blake2G.setupRow (fun _ => Vector.replicate 7 0)
    ⟨i.val, by have size := i.isLt; omega⟩
  #v[row[0], row[1], row[2], row[8]]

def setupTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 4) := .fromStatic {
  name := "Airbender.Blake2Round"
  length := 344384
  row i := (setupRow i).map (fun (n : Nat) => (n : ZMod p))
  index x := match x[3].val with
    | 4 => x[0].val * 256 + x[1].val
    | 17 => 65536 + x[0].val * 8 + x[1].val
    | 18 => 65600 + x[0].val * 16 + x[1].val
    | 19 => 65856 + x[0].val * 128 + x[1].val
    | 20 => 82240 + x[0].val * 512 + x[1].val
    | _ => 0
  Spec x := ∃ i : Fin 344384, x = (setupRow i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Blake2Round

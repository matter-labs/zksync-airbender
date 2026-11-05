import Human.Circuits.Blake2G.Tables.Setup

namespace Airbender.Blake2Round

/- Native regions of the extended-control round (table offsets from the upstream
   JSON, `blake2_with_extended_control`): XOR-8 (tag 4), XOR-7 (19) and XOR-9 (20)
   as in G, then three tables added for this circuit: XOR-8 with carry (55),
   XOR-7 with carry (56) and the split XOR (4+3)x(4+3) (57). Rows model
   cs/src/tables/binops.rs (create_xor_table, create_xor_with_carry_table,
   create_xor_4x3_table) and their index functions. Rust setup correspondence is
   deferred, as for G. -/

/-- Plain binary XOR rows, index = (a << width) | b, row = (a, b, a ^ b). -/
def xorRow (width tag index : Nat) : Vector Nat 6 :=
  let a := index / 2 ^ width
  let b := index % 2 ^ width
  #v[a, b, a ^^^ b, 0, 0, tag]

/-- XOR rows with a carry key in {0, 1, 2}, index = (carry << 2 * width) | (a << width) | b. -/
def xorCarryRow (width tag index : Nat) : Vector Nat 6 :=
  let rest := index % 2 ^ (2 * width)
  let a := rest / 2 ^ width
  let b := rest % 2 ^ width
  #v[a, b, index / 2 ^ (2 * width), a ^^^ b, 0, tag]

/-- Split (4+3)x(4+3) XOR rows, index = (a4 << 10) | (a3 << 7) | (b4 << 3) | b3,
    output = (a4 ^ b4) | ((a3 ^ b3) << 4). -/
def xor4x3Row (index : Nat) : Vector Nat 6 :=
  let a4 := index / 2 ^ 10
  let a3 := index / 2 ^ 7 % 2 ^ 3
  let b4 := index / 2 ^ 3 % 2 ^ 4
  let b3 := index % 2 ^ 3
  #v[a4, a3, b4, b3, (a4 ^^^ b4) ||| ((a3 ^^^ b3) <<< 4), 57]

/-- The 606208 native rows, in table-offset order. -/
def setupRow (index : Fin 606208) : Vector Nat 6 :=
  let n := index.val
  if n < 65536 then xorRow 8 4 n
  else if n < 81920 then xorRow 7 19 (n - 65536)
  else if n < 344064 then xorRow 9 20 (n - 81920)
  else if n < 540672 then xorCarryRow 8 55 (n - 344064)
  else if n < 589824 then xorCarryRow 7 56 (n - 540672)
  else xor4x3Row (n - 589824)

def setupTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 6) := .fromStatic {
  name := "Airbender.Blake2Round"
  length := 606208
  row i := (setupRow i).map (fun (n : Nat) => (n : ZMod p))
  index x := match x[5].val with
    | 4 => x[0].val * 256 + x[1].val
    | 19 => 65536 + x[0].val * 128 + x[1].val
    | 20 => 81920 + x[0].val * 512 + x[1].val
    | 55 => 344064 + x[2].val * 65536 + x[0].val * 256 + x[1].val
    | 56 => 540672 + x[2].val * 16384 + x[0].val * 128 + x[1].val
    | 57 => 589824 + x[0].val * 1024 + x[1].val * 128 + x[2].val * 8 + x[3].val
    | _ => 0
  Spec x := ∃ i : Fin 606208, x = (setupRow i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Blake2Round

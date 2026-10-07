import Airbender.Review.Lookups

namespace Airbender.Verification

/- Symbolic rows from cs/src/tables/memory_opcode_related.rs and rom_related.rs,
   selected by mem_subword_only/circuit.rs. Tags are from table_type.rs. This
   reconstructs the tables; extraction and Rust setup correspondence are deferred.
   `program` supplies independently fixed ROM words, including any padding. -/

def subwordLoadLimbs (byte : Bool) (key : Nat) : Nat × Nat :=
  let half := key % 65536
  let value := if byte then half / (if key / 131072 % 2 = 1 then 256 else 1) % 256 else half
  let negative := key / 65536 % 2 = 1 ∧ (if byte then 128 else 32768) ≤ value
  (value + (if byte && negative then 65280 else 0), if negative then 65535 else 0)

def subwordDataRow (key lo hi tag : Nat) : Vector Nat 9 :=
  #v[key, lo, hi, 0, 0, 0, 0, 0, tag]

/-- Tag 30 clears the selected old byte; tag 29 places the source's low byte. -/
def subwordStoreContribution (clear : Bool) (key : Nat) : Nat :=
  let half := key % 65536
  if clear then
    if key / 65536 % 2 = 1 then half % 256 else half - half % 256
  else (key % 256) * (if key / 65536 % 2 = 1 then 256 else 1)

def subwordRow (program : Nat → BitVec 32) (index : Fin 13238273) : Vector Nat 9 :=
  let n := index.val
  if n = 0 then subwordDataRow 0 0 0 0
  else if n < 131073 then
    let key := n - 1
    subwordDataRow key (subwordStoreContribution false key) 0 29
  else if n < 262145 then
    let key := n - 131073
    subwordDataRow key (subwordStoreContribution true key) 0 30
  else if n < 393217 then
    let key := n - 262145
    let data := subwordLoadLimbs false key
    subwordDataRow key data.1 data.2 42
  else if n < 655361 then
    let key := n - 393217
    let data := subwordLoadLimbs true key
    subwordDataRow key data.1 data.2 43
  else if n < 4849665 then
    let i := n - 655361
    let address := 4 * (i / 4)
    let signed := i / 2 % 2
    let half := (program (i / 4)).toNat / (if i % 2 = 1 then 65536 else 1) % 65536
    let data := subwordLoadLimbs false (half + 65536 * signed)
    subwordDataRow (address + 4194304 * signed + 8388608 * (i % 2)) data.1 data.2 44
  else
    let i := n - 4849665
    let address := 4 * (i / 8)
    let signed := i / 4 % 2
    let highHalf := i / 2 % 2
    let highByte := i % 2
    let half := (program (i / 8)).toNat / (if highHalf = 1 then 65536 else 1) % 65536
    let data := subwordLoadLimbs true (half + 65536 * signed + 131072 * highByte)
    subwordDataRow (address + 4194304 * signed + 8388608 * highHalf + 16777216 * highByte)
      data.1 data.2 45

def subwordTable {p : Nat} [Fact p.Prime] (program : Nat → BitVec 32) :
    Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.SubwordMemory"
  length := 13238273
  row i := (subwordRow program i).map (fun (n : Nat) => (n : ZMod p))
  index x := match x[8].val with
    | 29 => 1 + x[0].val
    | 30 => 131073 + x[0].val
    | 42 => 262145 + x[0].val
    | 43 => 393217 + x[0].val
    | 44 => 655361 + 4 * (x[0].val % 4194304 / 4) + 2 * (x[0].val / 4194304 % 2) +
        x[0].val / 8388608 % 2
    | 45 => 4849665 + 8 * (x[0].val % 4194304 / 4) + 4 * (x[0].val / 4194304 % 2) +
        2 * (x[0].val / 8388608 % 2) + x[0].val / 16777216 % 2
    | _ => 0
  Spec x := ∃ i : Fin 13238273, x = (subwordRow program i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Verification

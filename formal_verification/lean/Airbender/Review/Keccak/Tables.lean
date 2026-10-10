import Airbender.Review.Keccak.Artifact
import Airbender.Review.Properties
import Clean.Specs.Keccak256

namespace Airbender.Keccak

/- Symbolic reconstruction of cs/src/tables/keccak_precompile_related.rs and
   binops.rs. Rust-to-model setup correspondence remains unproved. Local claims parameterize control-index rows; native operation execution uses
   the concrete modeled rows in `Controller.lean`. Full scheduling is separate. -/

def adjustedConstant (round : Nat) : Nat :=
  if h : 0 < round ∧ round ≤ 24 then
    Specs.Keccak256.roundConstants[round - 1].toNat else 0

def iotaByte (control : Nat) : Nat :=
  (adjustedConstant (control % 32) / 2 ^ (8 * (control / 32))) % 256

def byteRow (tag index : Nat) : Vector Nat 8 :=
  let a := if tag = 4 then index / 256 else index % 256
  let b := if tag = 4 then index % 256 else index / 256
  let c := if tag = 38 then a ^^^ iotaByte b
    else if tag = 39 then (a ^^^ 255) &&& b else a ^^^ b
  #v[a, b, c, 0, 0, 0, 0, tag]

def rotationRow (key : Nat) : Vector Nat 8 :=
  let word := key % 65536
  let shift := key / 65536
  #v[key, word / 2 ^ (16 - shift), (word * 2 ^ shift) % 65536, 0, 0, 0, 0, 40]

def setupRow (control : Fin 4096 → Vector Nat 6) (index : Fin 1249281) : Vector Nat 8 :=
  let n := index.val
  if n = 0 then Vector.replicate 8 0
  else if n < 65537 then byteRow 4 (n - 1)
  else if h : n < 69633 then
    let key : Fin 4096 := ⟨n - 65537, by omega⟩
    let outputs := control key
    #v[key.val, outputs[0], outputs[1], outputs[2], outputs[3], outputs[4], outputs[5], 37]
  else if n < 135169 then byteRow 38 (n - 69633)
  else if n < 200705 then byteRow 39 (n - 135169)
  else rotationRow (n - 200705)

def setupTable {p : Nat} [Fact p.Prime] (control : Fin 4096 → Vector Nat 6) :
    Table (ZMod p) (fields 8) := .fromStatic {
  name := "Airbender.Keccak"
  length := 1249281
  row i := (setupRow control i).map (fun (n : Nat) => (n : ZMod p))
  index x := match x[7].val with
    | 4 => 1 + 256 * x[0].val + x[1].val
    | 37 => 65537 + x[0].val
    | 38 => 69633 + x[0].val + 256 * x[1].val
    | 39 => 135169 + x[0].val + 256 * x[1].val
    | 40 => 200705 + x[0].val
    | _ => 0
  Spec x := ∃ i : Fin 1249281, x = (setupRow control i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}
/-- Intended consequences of one tagged native query. These are properties of
    Clean membership, not another constraint interpreter. Tag zero is padding;
    rotation returns the two non-overlapping pieces of a packed 16-bit word. -/
def ByteOperationFacts (tag a b c : Nat) : Prop :=
  if tag = 0 then a = 0 ∧ b = 0 ∧ c = 0
  else if tag = 40 then
    a < 1048576 ∧ b < 65536 ∧ c < 65536 ∧
    b = (a % 65536) / 2 ^ (16 - a / 65536) ∧
    c = ((a % 65536) * 2 ^ (a / 65536)) % 65536
  else a < 256 ∧ b < 256 ∧ c < 256 ∧
    c = (if tag = 38 then a ^^^ iotaByte b
      else if tag = 39 then (a ^^^ 255) &&& b else a ^^^ b)

/-- Every native byte query has bounded, exact outputs, including padding.
    The table contents remain the modeled setup defined above. -/
def ByteLookupChecks {p : Nat} [Fact p.Prime]
    (control : Fin 4096 → Vector Nat 6) (w : Nat → ZMod p) : Prop :=
  ∀ i : Fin 40,
    let entry := ((FlatOperation.lookups (importedConstraints (setupTable control))).get
      ⟨i.val + 2, by rw [lookup_count]; omega⟩).entry.toArray
    let value := fun j => (entry[j]!.eval (Verification.environment w)).val
    ByteOperationFacts (value 7) (value 0) (value 1) (value 2)

end Airbender.Keccak


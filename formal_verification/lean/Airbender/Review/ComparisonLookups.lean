import Airbender.Review.RangeChecks

namespace Airbender.Verification

/- Symbolic reconstructions of Rust table rows, not extracted artifacts. Sources:
   cs/src/tables/integer_ops.rs and jump_branch_opcode_related.rs; table IDs in
   cs/src/definitions/table_type.rs. Rust-to-Lean table correspondence remains
   unproved, as for range16Table. Clean supplies the sole lookup semantics. -/

private def pairTable {p : Nat} [Fact p.Prime] (name : String)
    (length : Nat) (value : Nat → Nat) : Table (ZMod p) fieldPair := .fromStatic {
  name := name
  length := length
  row i := ((i.val : ZMod p), (value i.val : ZMod p))
  index x := x.1.val
  Spec x := ∃ i : Fin length, x = ((i.val : ZMod p), (value i.val : ZMod p))
  contains_iff _ := Iff.rfl
}

def regIsZeroTable {p : Nat} [Fact p.Prime] : Table (ZMod p) fieldPair :=
  pairTable "Airbender.RegIsZero" 131072 (fun n => if n = 0 then 1 else 0)

def u16SignTable {p : Nat} [Fact p.Prime] : Table (ZMod p) fieldPair :=
  pairTable "Airbender.U16GetSign" 65536 (fun n => n / 32768)

/-- Rust's standalone 22-bit conditional key: rs2 high limb, rs1 sign,
    unsigned less-than, equality, funct3. This is table behavior, not an ISA spec. -/
def conditionalValue (key : Nat) : Nat :=
  let rs2Negative := key / 32768 % 2 == 1
  let rs1Negative := key / 65536 % 2 == 1
  let unsignedLT := key / 131072 % 2 == 1
  let equal := key / 262144 % 2 == 1
  let signedLT := if rs1Negative && !rs2Negative then true
    else if !rs1Negative && rs2Negative then false else unsignedLT
  let resolved := match key / 524288 % 8 with
    | 0 => equal | 1 => !equal
    | 2 | 4 => signedLT
    | 3 | 6 => unsignedLT
    | 5 => !signedLT
    | _ => !unsignedLT
  if resolved then 1 else 0

def conditionalTable {p : Nat} [Fact p.Prime] : Table (ZMod p) fieldPair :=
  pairTable "Airbender.ConditionalJmpBranchSlt" 4194304 conditionalValue

def jumpCleanupTable {p : Nat} [Fact p.Prime] : Table (ZMod p) fieldTriple := .fromStatic {
  name := "Airbender.JumpCleanupOffset"
  length := 65536
  row i := ((i.val : ZMod p), ((i.val / 2 % 2 : Nat) : ZMod p), ((i.val - i.val % 4 : Nat) : ZMod p))
  index x := x.1.val
  Spec x := ∃ i : Fin 65536,
    x = ((i.val : ZMod p), ((i.val / 2 % 2 : Nat) : ZMod p), ((i.val - i.val % 4 : Nat) : ZMod p))
  contains_iff _ := Iff.rfl
}

def pairLookup {p : Nat} [Fact p.Prime] (table : Table (ZMod p) fieldPair)
    (key value : Expression (ZMod p)) : Lookup (ZMod p) where
  table := table.toRaw
  entry := #v[key, value]

def jumpCleanup {p : Nat} [Fact p.Prime]
    (key bit1 cleaned : Expression (ZMod p)) : Lookup (ZMod p) where
  table := jumpCleanupTable.toRaw
  entry := #v[key, bit1, cleaned]

end Airbender.Verification

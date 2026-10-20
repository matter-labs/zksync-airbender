import Human.Helpers.Tables.Range

namespace Airbender.Verification

/- Symbolic reconstructions of Rust table rows, not extracted artifacts. Sources:
   cs/src/tables/integer_ops.rs and jump_branch_opcode_related.rs; table IDs in
   cs/src/definitions/table_type.rs. Rust-to-Lean table correspondence remains
   unproved, as for range16Table. Clean supplies the sole lookup semantics. -/

def pairTable {p : Nat} [Fact p.Prime] (name : String)
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

/-- Rust `create_u16_get_low_byte_table`, table ID 41: (n, n mod 256).
    Like the other fixed tables, this is modeled, not extracted. -/
def u16LowByteTable {p : Nat} [Fact p.Prime] : Table (ZMod p) fieldPair :=
  pairTable "Airbender.U16GetLowByte" 65536 (fun n => n % 256)

def pairLookup {p : Nat} [Fact p.Prime] (table : Table (ZMod p) fieldPair)
    (key value : Expression (ZMod p)) : Lookup (ZMod p) where
  table := table.toRaw
  entry := #v[key, value]


end Airbender.Verification

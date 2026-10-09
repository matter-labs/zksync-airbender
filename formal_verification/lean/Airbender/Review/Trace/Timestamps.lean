import Airbender.Review.RangeChecks

namespace Airbender.Trace

/-- Airbender's RAM/state clock has two 19-bit limbs; row accesses use offsets
    0, 1, 2 and the next machine state advances by four. -/
abbrev timestampBase : Nat := 524288

/-- A native timestamp represented by two natural limbs. `value` combines
    them; `Bounded` separately requires both to fit in the 19-bit base. -/
structure Timestamp where
  lo : Nat
  hi : Nat
  deriving DecidableEq

def Timestamp.value (t : Timestamp) : Nat := t.lo + timestampBase * t.hi

def Timestamp.Bounded (t : Timestamp) : Prop := t.lo < timestampBase ∧ t.hi < timestampBase

/-- Interpret the field values in imported clock `columns` as natural limbs.
    Canonical field residues are not automatically 19-bit; lookups/history prove that bound. -/
def decodeTimestamp {p : Nat} (w : Nat → ZMod p) (columns : Vector Nat 2) : Timestamp :=
  ⟨(w columns[0]).val, (w columns[1]).val⟩

/-- Rust's `TIMESTAMP_COLUMNS_NUM_BITS` in `common_constants/src/timestamps.rs`;
    `VirtualSetupPoly::RangeCheckTimestamp` uses the virtual range setup. As with
    the other range tables, correspondence to that Rust setup remains unproved. -/
def timestampTable {p : Nat} [Fact p.Prime] : Table (ZMod p) field :=
  Verification.rangeTable "Airbender.Timestamp19" timestampBase

def timestampLookup {p : Nat} [Fact p.Prime] (entry : Expression (ZMod p)) : Lookup (ZMod p) :=
  ⟨timestampTable.toRaw, #v[entry]⟩

end Airbender.Trace

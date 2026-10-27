/-!
# Field capacity conditions

These transparent names state inequalities, including their strictness.
They describe canonical-value/no-wrap room; they neither select a characteristic
nor assert that an imported artifact was exported for that field. In particular,
capacity alone is generic. Fixed imported inverse coefficients have a
separate compatibility interface in `SerializedInverse`.
-/

namespace Airbender.FieldCapacity

/-- The field has at least `required` distinct canonical residues. -/
abbrev AtLeast (p required : Nat) : Prop := required ≤ p

/-- The inclusive bound `bound` is strictly below the characteristic. -/
abbrev NoWrap (p bound : Nat) : Prop := bound < p

/-- Room for a two-limb clock comparison and native access/retirement offsets.
The base remains a parameter; no particular characteristic is selected. -/
abbrev ClockNoWrap (p base : Nat) : Prop := 2 * base + 4 < p

/-- 29-bit capacity of pooled native word/clock contracts. This does
not require an entire RV32 word to fit in one field element. -/
abbrev NativeWordCapacity (p : Nat) : Prop := 536870912 ≤ p

/-- 22-bit capacity of native ROM/decoder and unified-row contracts. -/
abbrev NativeRomCapacity (p : Nat) : Prop := 4194304 ≤ p

/-- 23-bit capacity of the native hash-worker composition contracts. -/
abbrev NativeHashCapacity (p : Nat) : Prop := 8388608 ≤ p

/-- 24-bit capacity used by the wider native hash/Keccak composition. -/
abbrev NativeWideHashCapacity (p : Nat) : Prop := 16777216 ≤ p

end Airbender.FieldCapacity

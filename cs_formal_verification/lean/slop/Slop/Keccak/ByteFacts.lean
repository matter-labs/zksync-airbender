module
public import Slop.Keccak.FixedLookups
public import Slop.Keccak.OpIndex
public import Slop.Eval
public import Slop.CleanCore.Circuit.Operations
public import Slop.Defs.Circuits.Keccak.Artifact
public import Slop.Defs.Circuits.Keccak.Tables.Setup

@[expose] public section

/-! The byte query of operation `operation`, byte `byte`, proven once for every index: its value
columns are the operation's input and output bytes, and with mode `mode` selected its relation is the
one of that mode's routing tag. -/

namespace Airbender.Keccak.Proofs
open Arithmetic
set_option warningAsError true

/-- The byte query's three value columns are the input and output words of byte `i`. -/
theorem byte_columns {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8))
    (w : Nat → ZMod p) (i : Fin 40) :
    ((byteQuery setup i).entry.toArray[0]!).eval (Verification.environment w) =
      w (102 + 24 * (i.val / 8) + i.val % 8) ∧
    ((byteQuery setup i).entry.toArray[1]!).eval (Verification.environment w) =
      w (110 + 24 * (i.val / 8) + i.val % 8) ∧
    ((byteQuery setup i).entry.toArray[2]!).eval (Verification.environment w) =
      w (118 + 24 * (i.val / 8) + i.val % 8) := by
  fin_cases i
  all_goals simp only [byteQuery]
  all_goals op_index
  all_goals eval_entry [Fin.val_mk, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.zero_div,
    Nat.div_self, and_self, Nat.reduceLT, Nat.ofNat_pos, Nat.one_lt_ofNat]

/-- The tag column of a byte query is the byte tag. -/
theorem byte_tag_column {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8))
    (w : Nat → ZMod p) (i : Fin 40) :
    byteTag setup w i = ((byteQuery setup i).entry.toArray[7]!).eval (Verification.environment w) := by
  unfold byteTag
  simp only [Array.back!, Vector.size_toArray, byte_query_arity]

/-- With mode `mode` selected, byte `byte` of operation `operation` satisfies the relation of the
    mode's routing tag for that operation. -/
theorem selected_byte_facts {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (mode : Fin 7) (selected : w Variables.modeColumns[mode] = 1)
    (operation : Fin 5) (byte : Fin 8) :
    ByteOperationFacts operationTags[mode][operation.val]
      (w (102 + 24 * operation.val + byte.val)).val
      (w (110 + 24 * operation.val + byte.val)).val
      (w (118 + 24 * operation.val + byte.val)).val := by
  have query := byte_lookup_checks hp h
  unfold ByteLookupChecks at query
  have tags := selected_tags (by omega) h active mode selected ⟨8 * operation.val + byte.val, by omega⟩
  have ho : (8 * operation.val + byte.val) / 8 = operation.val := by omega
  have hb : (8 * operation.val + byte.val) % 8 = byte.val := by omega
  obtain ⟨c0, c1, c2⟩ := byte_columns (setupTable control) w ⟨8 * operation.val + byte.val, by omega⟩
  simp only [ho, hb] at c0 c1 c2 tags
  have tagValue : ((byteQuery (setupTable control) ⟨8 * operation.val + byte.val, by omega⟩).entry.toArray[7]!.eval
      (Verification.environment w)).val = operationTags[mode][operation.val] := by
    rw [← byte_tag_column, tags]
  have q : ByteOperationFacts
      ((byteQuery (setupTable control) ⟨8 * operation.val + byte.val, by omega⟩).entry.toArray[7]!.eval
        (Verification.environment w)).val
      ((byteQuery (setupTable control) ⟨8 * operation.val + byte.val, by omega⟩).entry.toArray[0]!.eval
        (Verification.environment w)).val
      ((byteQuery (setupTable control) ⟨8 * operation.val + byte.val, by omega⟩).entry.toArray[1]!.eval
        (Verification.environment w)).val
      ((byteQuery (setupTable control) ⟨8 * operation.val + byte.val, by omega⟩).entry.toArray[2]!.eval
        (Verification.environment w)).val := query ⟨8 * operation.val + byte.val, by omega⟩
  rwa [tagValue, c0, c1, c2] at q

/-- An XOR byte query (tag 4). -/
theorem xor_byte_facts {a b c : Nat} (facts : ByteOperationFacts 4 a b c) :
    a < 256 ∧ b < 256 ∧ c < 256 ∧ c = a ^^^ b := by
  simpa only [ByteOperationFacts, OfNat.ofNat_ne_zero, Nat.reduceEqDiff, ↓reduceIte] using facts

/-- An Iota-XOR byte query (tag 38). -/
theorem iota_byte_facts {a b c : Nat} (facts : ByteOperationFacts 38 a b c) :
    a < 256 ∧ b < 256 ∧ c < 256 ∧ c = a ^^^ iotaByte b := by
  simpa only [ByteOperationFacts, OfNat.ofNat_ne_zero, Nat.reduceEqDiff, ↓reduceIte] using facts

/-- An ANDN byte query (tag 39). -/
theorem andn_byte_facts {a b c : Nat} (facts : ByteOperationFacts 39 a b c) :
    a < 256 ∧ b < 256 ∧ c < 256 ∧ c = (a ^^^ 255) &&& b := by
  simpa only [ByteOperationFacts, OfNat.ofNat_ne_zero, Nat.reduceEqDiff, ↓reduceIte] using facts

/-- A rotation byte query (tag 40): the split of a rotated limb. -/
theorem rotation_byte_facts {a b c : Nat} (facts : ByteOperationFacts 40 a b c) :
    a < 1048576 ∧ b < 65536 ∧ c < 65536 ∧ b = (a % 65536) / 2 ^ (16 - a / 65536) ∧
      c = ((a % 65536) * 2 ^ (a / 65536)) % 65536 := by
  simpa only [ByteOperationFacts, OfNat.ofNat_ne_zero, ↓reduceIte] using facts

end Airbender.Keccak.Proofs

import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Keccak.Tables
import Airbender.Proofs.Keccak.Tags

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

/-- The imported table and all its byte entries have eight columns. -/
theorem byte_query_arity {p : Nat} [Fact p.Prime]
    (setup : Table (ZMod p) (fields 8)) (i : Fin 40) :
    (byteQuery setup i).table.arity = 8 := by
  fin_cases i <;> rfl

/-- Cast the complete native entry to its checked width, without translating it. -/
def byteEntry {p : Nat} [Fact p.Prime]
    (setup : Table (ZMod p) (fields 8)) (i : Fin 40) : Vector (Expression (ZMod p)) 8 :=
  (byteQuery setup i).entry.cast (byte_query_arity setup i)

/-- Every emitted byte query has the complete eight-column tagged shape. -/
theorem byte_query_shape {p : Nat} [Fact p.Prime]
    (setup : Table (ZMod p) (fields 8)) (i : Fin 40) :
    byteQuery setup i = Lookup.mk setup.toRaw (byteEntry setup i) := by
  fin_cases i <;> rfl

/-- Theta mode routes all five eight-byte operations through the modeled XOR
    table. Membership derives both source ranges, result ranges and exact XOR. -/
theorem theta_byte_relations {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 256)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable (p := p) control)))
    (active : w 0 = 1) (theta : w 66 = 1) (i : Fin 40) :
    let entry := (byteQuery (setupTable (p := p) control) i).entry.toArray
    (entry[0]!.eval (Verification.environment w)).val < 256 ∧
    (entry[1]!.eval (Verification.environment w)).val < 256 ∧
    (entry[2]!.eval (Verification.environment w)).val < 256 ∧
    (entry[2]!.eval (Verification.environment w)).val =
      (entry[0]!.eval (Verification.environment w)).val ^^^
        (entry[1]!.eval (Verification.environment w)).val := by
  have tags := selected_tags (by omega) holds active (3 : Fin 7) theta i
  have tags4 : (byteTag (setupTable (p := p) control) w i).val = 4 := by
    fin_cases i <;> simpa [operationTags] using tags
  have tagField : byteTag (setupTable (p := p) control) w i = 4 := by
    have cast := ZMod.natCast_zmod_val (byteTag (setupTable (p := p) control) w i)
    rw [tags4] at cast
    simpa only [Nat.cast_ofNat] using cast.symm
  have member := Verification.lookup_of_holds holds
    ⟨i.val + 2, by rw [lookup_count]; omega⟩
  change (byteQuery (setupTable (p := p) control) i).Contains (Verification.environment w) at member
  let entry := byteEntry (setupTable (p := p) control) i
  have shape : byteQuery (setupTable (p := p) control) i =
      Lookup.mk (setupTable (p := p) control).toRaw entry :=
    byte_query_shape (setupTable (p := p) control) i
  have column (j : Nat) (hj : j < 8) : entry.toArray[j]! = entry[j] := by
    rw [getElem!_pos entry.toArray j (by simpa only [Vector.size_toArray] using hj)]
    rfl
  unfold byteTag at tagField
  rw [shape] at tagField
  have tagged : entry[7].eval (Verification.environment w) = 4 := by
    simp only [Array.back!, Vector.size_toArray] at tagField
    change entry.toArray[7]!.eval (Verification.environment w) = 4 at tagField
    rw [column 7 (by decide)] at tagField
    exact tagField
  rw [shape] at member
  have relation := xor_lookup hp member tagged
  rw [shape]
  simpa only [Lookup.entry, column 0 (by decide), column 1 (by decide),
    column 2 (by decide)] using relation

end Airbender.Keccak.Proofs

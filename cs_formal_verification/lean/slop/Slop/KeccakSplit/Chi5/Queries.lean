module
public import Slop.KeccakSplit.Chi5.OpIndex
public import Slop.KeccakSplit.Setup.Chi5.Members
public import Slop.KeccakSplit.Memory.Order
public import Slop.Constraints
public import Slop.Trace.Timestamps
public import Slop.Arithmetic.Chunks

@[expose] public section

/- The chi5 worker's imported queries over BabyBear: the alignment query (lookup 0),
   the controller query (1) and the sixteen nibble chi queries (2–17), read through
   the exported setup's row meaning (`Setup/Chi5/Members`). -/

namespace Airbender.Keccak.Split.Chi5.Proofs
open Airbender.Trace Airbender.Keccak.Split.Proofs
set_option warningAsError true

/-- The worker's equations and queries hold on `w`. -/
abbrev Holds (w : Nat → ZMod babyBearModulus) : Prop :=
  FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Chi5.clockConstraints (Chi5.setup (p := babyBearModulus)))

theorem core {w : Nat → ZMod babyBearModulus} (h : Holds w) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.importedConstraints (Chi5.setup (p := babyBearModulus))) :=
  Verification.holds_of_sublist h (List.sublist_append_left _ _)

/-- The register-ten high limbs (read and written) are zero. -/
theorem control_high {w : Nat → ZMod babyBearModulus} (h : Holds w) : w 4 = 0 ∧ w 6 = 0 := by
  have read := Verification.assertion_of_holds (core h) ⟨1, by decide⟩
  have write := Verification.assertion_of_holds (core h) ⟨2, by decide⟩
  op_index at read write
  simp only [Expression.eval, Verification.environment] at read write
  exact ⟨read, write⟩

/-- The alignment query: the x11 low limb is `256 * y` with `y` in the timestamp range. -/
theorem pointer_aligned {w : Nat → ZMod babyBearModulus} (h : Holds w) : (w 12).val % 256 = 0 := by
  have query := Verification.lookup_of_holds (core h) ⟨0, by decide⟩
  op_index at query
  have bound := Trace.Proofs.range_bound query
  simp [Expression.eval, Verification.environment] at bound
  have value := Arithmetic.value_of_scaled_range
    (by decide : 256 * Trace.timestampBase ≤ babyBearModulus) (by decide)
    (by decide : ((256 : Nat) : ZMod babyBearModulus) * (-7864320) = 1)
    (by simpa only [neg_mul] using bound)
  rw [value]
  simp

theorem control_entries (w : Nat → ZMod babyBearModulus) :
    let row := ((chi5ControlQuery (p := babyBearModulus)).entry.cast chi5_control_arity).map
      (Expression.eval (Verification.environment w))
    row[0] = w 3 ∧ row[2] = w 5 ∧ ∀ lane : Fin 5, row[3 + lane.val] = w (7 + lane.val) := by
  intro row
  refine ⟨?_, ?_, fun lane => ?_⟩
  · simp only [row]; rw [getElem_cast_map]
    simp only [chi5ControlQuery]; op_index; simp [Expression.eval, Verification.environment]
  · simp only [row]; rw [getElem_cast_map]
    simp only [chi5ControlQuery]; op_index; simp [Expression.eval, Verification.environment]
  · simp only [row]; rw [getElem_cast_map]
    simp only [chi5ControlQuery]
    fin_cases lane <;> op_index <;> simp [Expression.eval, Verification.environment]

/-- An active row's controller query is a controller row of call `index`. -/
theorem controller {w : Nat → ZMod babyBearModulus} (h : Holds w) (active : w 0 = 1) :
    ∃ index : Fin 361, kindAt index.val = .chi5 ∧
      w 3 = (controlAt index.val : ZMod babyBearModulus) ∧
      w 5 = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      ∀ lane : Fin 5, w (7 + lane.val) =
        ((Call.slots index)[lane.val].val : ZMod babyBearModulus) := by
  have lookup : (chi5ControlQuery (p := babyBearModulus)).Contains (Verification.environment w) :=
    Verification.lookup_of_holds (core h) _
  rw [chi5_control_shape] at lookup
  have sound : (Chi5.setup (p := babyBearModulus)).toRaw.Soundness #[] _ :=
    (Chi5.setup (p := babyBearModulus)).toRaw.imply_soundness _ _ lookup
  obtain ⟨tag, enabled, _⟩ := chi5_control_entries w
  obtain ⟨c0, c2, cs⟩ := control_entries w
  obtain ⟨index, kind, e0, e2, slots, _⟩ :=
    Chi5.SetupProofs.control_table_sound sound tag (enabled.trans active)
  refine ⟨index, kind, c0 ▸ e0, c2 ▸ e2, fun lane => ?_⟩
  rw [← cs lane]
  exact slots lane

/-- Nibble query `digit` (lookup 2 + digit). -/
noncomputable def nibbleQuery (digit : Fin 16) : Lookup (ZMod babyBearModulus) :=
  (FlatOperation.lookups (Chi5.importedConstraints (Chi5.setup (p := babyBearModulus)))).get
    ⟨2 + digit.val, by rw [chi5_lookup_count]; omega⟩

theorem nibble_arity (digit : Fin 16) : (nibbleQuery digit).table.arity = 11 := by
  fin_cases digit <;> rfl

theorem nibble_shape (digit : Fin 16) :
    nibbleQuery digit = Lookup.mk (Chi5.setup (p := babyBearModulus)).toRaw
      ((nibbleQuery digit).entry.cast (nibble_arity digit)) := by
  fin_cases digit <;> rfl

/-- The evaluated row of nibble query `digit`: five input nibbles, five chi nibbles, tag. -/
noncomputable def nibbleRow (w : Nat → ZMod babyBearModulus) (digit : Fin 16) :
    Vector (ZMod babyBearModulus) 11 :=
  ((nibbleQuery digit).entry.cast (nibble_arity digit)).map
    (Expression.eval (Verification.environment w))

theorem nibble_tag (w : Nat → ZMod babyBearModulus) (digit : Fin 16) :
    (nibbleRow w digit)[10] = 65 := by
  simp only [nibbleRow]; rw [getElem_cast_map]
  simp only [nibbleQuery]
  fin_cases digit <;> op_index <;> simp [Expression.eval, Verification.environment]

/-- Every nibble query is a chi table row: bounded nibbles and chi on each. -/
theorem nibble_facts {w : Nat → ZMod babyBearModulus} (h : Holds w) (digit : Fin 16) :
    (∀ c : Fin 5, (nibbleRow w digit)[c.val].val < 16) ∧
      (∀ c : Fin 5, (nibbleRow w digit)[5 + c.val].val < 16 ∧
        (nibbleRow w digit)[5 + c.val].val = (nibbleRow w digit)[c.val].val ^^^
          ((15 ^^^ (nibbleRow w digit)[(c.val + 1) % 5].val) &&&
            (nibbleRow w digit)[(c.val + 2) % 5].val)) := by
  have lookup : (nibbleQuery digit).Contains (Verification.environment w) :=
    Verification.lookup_of_holds (core h) _
  rw [nibble_shape] at lookup
  have sound : (Chi5.setup (p := babyBearModulus)).toRaw.Soundness #[] (nibbleRow w digit) :=
    (Chi5.setup (p := babyBearModulus)).toRaw.imply_soundness _ _ lookup
  exact Chi5.SetupProofs.chi_table_sound sound (nibble_tag w digit)

end Airbender.Keccak.Split.Chi5.Proofs

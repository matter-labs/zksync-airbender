import Slop.KeccakSplit.ColumnParity.OpIndex
import Slop.KeccakSplit.Setup.ColumnParity.Members
import Slop.KeccakSplit.Memory.Order
import Slop.KeccakSplit.RowCommon
import Slop.Constraints
import Slop.Trace.Timestamps
import Slop.Arithmetic.Chunks

/- The column-parity worker's imported queries over BabyBear: the alignment query
   (lookup 0), then the 22 setup queries `query i` = lookup 1 + i: slots (i = 0),
   controller (1), four iota byte queries (2–5), sixteen five-input XOR nibble
   queries (6–21). -/

namespace Airbender.Keccak.Split.ColumnParity.Proofs
open Airbender.Trace Airbender.Keccak.Split.Proofs Airbender.Keccak.Split.RowProofs
set_option warningAsError true

abbrev Holds (w : Nat → ZMod babyBearModulus) : Prop :=
  FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (ColumnParity.clockConstraints (ColumnParity.setup (p := babyBearModulus)))

theorem core {w : Nat → ZMod babyBearModulus} (h : Holds w) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ColumnParity.importedConstraints (ColumnParity.setup (p := babyBearModulus))) :=
  Verification.holds_of_sublist h (List.sublist_append_left _ _)

theorem lookup_count :
    (FlatOperation.lookups (ColumnParity.importedConstraints
      (ColumnParity.setup (p := babyBearModulus)))).length = 23 := rfl

theorem control_high {w : Nat → ZMod babyBearModulus} (h : Holds w) : w 4 = 0 ∧ w 6 = 0 := by
  have read := Verification.assertion_of_holds (core h) ⟨1, by decide⟩
  have write := Verification.assertion_of_holds (core h) ⟨2, by decide⟩
  op_index at read write
  simp only [Expression.eval, Verification.environment] at read write
  exact ⟨read, write⟩

theorem pointer_aligned {w : Nat → ZMod babyBearModulus} (h : Holds w) : (w 13).val % 256 = 0 := by
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

/-- Setup query `i` (lookup 1 + i). -/
noncomputable def query (i : Fin 22) : Lookup (ZMod babyBearModulus) :=
  (FlatOperation.lookups (ColumnParity.importedConstraints (ColumnParity.setup (p := babyBearModulus)))).get
    ⟨1 + i.val, by rw [lookup_count]; omega⟩

theorem query_arity (i : Fin 22) : (query i).table.arity = 8 := by
  fin_cases i <;> rfl

theorem query_shape (i : Fin 22) :
    query i = Lookup.mk (ColumnParity.setup (p := babyBearModulus)).toRaw
      ((query i).entry.cast (query_arity i)) := by
  fin_cases i <;> rfl

/-- The evaluated row of setup query `i`. -/
noncomputable def row (w : Nat → ZMod babyBearModulus) (i : Fin 22) : Vector (ZMod babyBearModulus) 8 :=
  ((query i).entry.cast (query_arity i)).map (Expression.eval (Verification.environment w))

theorem row_entry (w : Nat → ZMod babyBearModulus) (i : Fin 22) (c : Nat) (hc : c < 8) :
    (row w i)[c] = Expression.eval (Verification.environment w) ((query i).entry.toArray[c]!) :=
  getElem_cast_map _ _ _ _ _

theorem row_sound {w : Nat → ZMod babyBearModulus} (h : Holds w) (i : Fin 22) :
    (ColumnParity.setup (p := babyBearModulus)).toRaw.Soundness #[] (row w i) := by
  have lookup : (query i).Contains (Verification.environment w) :=
    Verification.lookup_of_holds (core h) _
  rw [query_shape] at lookup
  exact (ColumnParity.setup (p := babyBearModulus)).toRaw.imply_soundness _ _ lookup

/-- Evaluate one entry of a setup query to its witness expression. -/
macro "entry_eval" : tactic =>
  `(tactic| (rw [row_entry]; simp only [query, Fin.val_one]; (op_index); simp [Expression.eval, Verification.environment]))

theorem slot_tag (w : Nat → ZMod babyBearModulus) : (row w 0)[7] = 62 := by entry_eval
theorem control_tag (w : Nat → ZMod babyBearModulus) : (row w 1)[7] = 63 := by entry_eval

theorem iota_tag (w : Nat → ZMod babyBearModulus) (j : Fin 4) :
    (row w ⟨2 + j.val, by omega⟩)[7] = 38 := by
  fin_cases j <;> entry_eval

theorem xor_tag (w : Nat → ZMod babyBearModulus) (d : Fin 16) :
    (row w ⟨6 + d.val, by omega⟩)[7] = 64 := by
  fin_cases d <;> entry_eval

theorem control_entries (w : Nat → ZMod babyBearModulus) :
    (row w 1)[0] = w 3 ∧ (row w 1)[1] = w 0 ∧ (row w 1)[2] = w 5 ∧ (row w 1)[3] = w 47 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> entry_eval

theorem slot_entries (w : Nat → ZMod babyBearModulus) :
    (row w 0)[0] = 2048 * w 0 + w 3 ∧ ∀ lane : Fin 6, (row w 0)[1 + lane.val] = w (7 + lane.val) := by
  refine ⟨?_, fun lane => ?_⟩
  · entry_eval
  · fin_cases lane <;> entry_eval

/-- An active row's controller and slot queries are those of call `index`. -/
theorem controller {w : Nat → ZMod babyBearModulus} (h : Holds w) (active : w 0 = 1) :
    ∃ index : Fin 361, kindAt index.val = .columnParity ∧
      w 3 = (controlAt index.val : ZMod babyBearModulus) ∧
      w 5 = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      w 47 = ((if index.val % 5 = 0 then index.val / 15 else 0 : Nat) : ZMod babyBearModulus) ∧
      ∀ lane : Fin 6, w (7 + lane.val) =
        ((Call.slots index)[lane.val].val : ZMod babyBearModulus) := by
  obtain ⟨c0, c1, c2, c3⟩ := control_entries w
  obtain ⟨s0, ss⟩ := slot_entries w
  obtain ⟨index, kind, e0, e2, e3⟩ := ColumnParity.SetupProofs.control_table_sound
    (row_sound h 1) (control_tag w) (c1.trans active)
  rw [c0] at e0
  rw [c2] at e2
  rw [c3] at e3
  have key : (row w 0)[0] = ((controlAt index.val + 2048 : Nat) : ZMod babyBearModulus) := by
    rw [s0, active, e0]; push_cast; ring
  have slots := ColumnParity.SetupProofs.slot_table_sound (row_sound h 0) (slot_tag w) index key
  refine ⟨index, kind, e0, e2, e3, fun lane => ?_⟩
  rw [← ss lane]
  exact slots lane

/-- Five-input XOR nibble query `d`. -/
theorem xor_facts {w : Nat → ZMod babyBearModulus} (h : Holds w) (d : Fin 16) :
    (∀ c : Fin 5, (row w ⟨6 + d.val, by omega⟩)[c.val].val < 16) ∧
      (row w ⟨6 + d.val, by omega⟩)[5].val < 16 ∧
      (row w ⟨6 + d.val, by omega⟩)[5].val = (row w ⟨6 + d.val, by omega⟩)[0].val ^^^
        (row w ⟨6 + d.val, by omega⟩)[1].val ^^^ (row w ⟨6 + d.val, by omega⟩)[2].val ^^^
        (row w ⟨6 + d.val, by omega⟩)[3].val ^^^ (row w ⟨6 + d.val, by omega⟩)[4].val := by
  obtain ⟨a, b, c, -⟩ := ColumnParity.SetupProofs.xor5_table_sound (row_sound h _) (xor_tag w d)
  exact ⟨a, b, c⟩

/-- Iota byte query `j`: bounded bytes and `out = in ^ iotaByte key`. -/
theorem iota_facts {w : Nat → ZMod babyBearModulus} (h : Holds w) (j : Fin 4) :
    (row w ⟨2 + j.val, by omega⟩)[0].val < 256 ∧ (row w ⟨2 + j.val, by omega⟩)[1].val < 256 ∧
      (row w ⟨2 + j.val, by omega⟩)[2].val < 256 ∧
      (row w ⟨2 + j.val, by omega⟩)[2].val = (row w ⟨2 + j.val, by omega⟩)[0].val ^^^
        Airbender.Keccak.iotaByte (row w ⟨2 + j.val, by omega⟩)[1].val := by
  obtain ⟨a, b, c, d, -⟩ := ColumnParity.SetupProofs.iota_table_sound (row_sound h _) (iota_tag w j)
  exact ⟨a, b, c, d⟩

end Airbender.Keccak.Split.ColumnParity.Proofs

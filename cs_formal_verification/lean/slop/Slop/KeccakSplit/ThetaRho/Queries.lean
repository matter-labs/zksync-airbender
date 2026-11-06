import Slop.KeccakSplit.ThetaRho.OpIndex
import Slop.KeccakSplit.Setup.ThetaRho.Members
import Slop.KeccakSplit.Memory.Order
import Slop.KeccakSplit.RowCommon
import Slop.Constraints
import Slop.Trace.Timestamps
import Slop.Arithmetic.Chunks

/- The theta/rho worker's imported queries over BabyBear: the alignment query
   (lookup 0), then the 50 setup queries `query i` = lookup 1 + i: slots (i = 0),
   eight D-byte XOR queries (1–8), controller (9), forty XOR-and-split queries
   (10 + 8·lane + byte). -/

namespace Airbender.Keccak.Split.ThetaRho.Proofs
open Airbender.Trace Airbender.Keccak.Split.Proofs Airbender.Keccak.Split.RowProofs
set_option warningAsError true

abbrev Holds (w : Nat → ZMod babyBearModulus) : Prop :=
  FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (ThetaRho.clockConstraints (ThetaRho.setup (p := babyBearModulus)))

theorem core {w : Nat → ZMod babyBearModulus} (h : Holds w) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.importedConstraints (ThetaRho.setup (p := babyBearModulus))) :=
  Verification.holds_of_sublist h (List.sublist_append_left _ _)

theorem lookup_count :
    (FlatOperation.lookups (ThetaRho.importedConstraints
      (ThetaRho.setup (p := babyBearModulus)))).length = 51 := rfl

theorem control_high {w : Nat → ZMod babyBearModulus} (h : Holds w) : w 4 = 0 ∧ w 6 = 0 := by
  have read := Verification.assertion_of_holds (core h) ⟨1, by decide⟩
  have write := Verification.assertion_of_holds (core h) ⟨2, by decide⟩
  op_index at read write
  simp only [Expression.eval, Verification.environment] at read write
  exact ⟨read, write⟩

theorem pointer_aligned {w : Nat → ZMod babyBearModulus} (h : Holds w) : (w 14).val % 256 = 0 := by
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
noncomputable def query (i : Fin 50) : Lookup (ZMod babyBearModulus) :=
  (FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := babyBearModulus)))).get
    ⟨1 + i.val, by rw [lookup_count]; omega⟩

theorem query_arity (i : Fin 50) : (query i).table.arity = 9 := by
  fin_cases i <;> rfl

theorem query_shape (i : Fin 50) :
    query i = Lookup.mk (ThetaRho.setup (p := babyBearModulus)).toRaw
      ((query i).entry.cast (query_arity i)) := by
  fin_cases i <;> rfl

/-- The evaluated row of setup query `i`. -/
noncomputable def row (w : Nat → ZMod babyBearModulus) (i : Fin 50) : Vector (ZMod babyBearModulus) 9 :=
  ((query i).entry.cast (query_arity i)).map (Expression.eval (Verification.environment w))

theorem row_entry (w : Nat → ZMod babyBearModulus) (i : Fin 50) (c : Nat) (hc : c < 9) :
    (row w i)[c] = Expression.eval (Verification.environment w) ((query i).entry.toArray[c]!) :=
  getElem_cast_map _ _ _ _ _

theorem row_sound {w : Nat → ZMod babyBearModulus} (h : Holds w) (i : Fin 50) :
    (ThetaRho.setup (p := babyBearModulus)).toRaw.Soundness #[] (row w i) := by
  have lookup : (query i).Contains (Verification.environment w) :=
    Verification.lookup_of_holds (core h) _
  rw [query_shape] at lookup
  exact (ThetaRho.setup (p := babyBearModulus)).toRaw.imply_soundness _ _ lookup

/-- Evaluate one entry of a setup query to its witness expression. -/
macro "entry_eval" : tactic =>
  `(tactic| (rw [row_entry]; simp only [query, Fin.val_one]; (op_index); simp [Expression.eval, Verification.environment]))

theorem slot_tag (w : Nat → ZMod babyBearModulus) : (row w 0)[8] = 60 := by entry_eval
theorem control_tag (w : Nat → ZMod babyBearModulus) : (row w ⟨9, by decide⟩)[8] = 59 := by entry_eval

theorem xor_tag (w : Nat → ZMod babyBearModulus) (d : Fin 8) :
    (row w ⟨1 + d.val, by omega⟩)[8] = 4 := by
  fin_cases d <;> entry_eval

theorem split_tag (w : Nat → ZMod babyBearModulus) (i : Fin 40) :
    (row w ⟨10 + i.val, by omega⟩)[8] = 58 := by
  fin_cases i <;> entry_eval

theorem control_entries (w : Nat → ZMod babyBearModulus) :
    (row w ⟨9, by decide⟩)[0] = w 3 ∧ (row w ⟨9, by decide⟩)[1] = w 0 ∧
      (row w ⟨9, by decide⟩)[2] = w 5 ∧
      ∀ c : Fin 5, (row w ⟨9, by decide⟩)[3 + c.val] = w (84 + c.val) := by
  refine ⟨?_, ?_, ?_, fun c => ?_⟩
  · entry_eval
  · entry_eval
  · entry_eval
  · fin_cases c <;> entry_eval

theorem slot_entries (w : Nat → ZMod babyBearModulus) :
    (row w 0)[0] = 2048 * w 0 + w 3 ∧ ∀ lane : Fin 7, (row w 0)[1 + lane.val] = w (7 + lane.val) := by
  refine ⟨?_, fun lane => ?_⟩
  · entry_eval
  · fin_cases lane <;> entry_eval

/-- An active row's controller and slot queries are those of call `index`. -/
theorem controller {w : Nat → ZMod babyBearModulus} (h : Holds w) (active : w 0 = 1) :
    ∃ index : Fin 361, kindAt index.val = .thetaRho ∧
      w 3 = (controlAt index.val : ZMod babyBearModulus) ∧
      w 5 = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ c : Fin 5, w (84 + c.val) = if c.val = index.val % 5 then 1 else 0) ∧
      ∀ lane : Fin 7, w (7 + lane.val) =
        ((Call.slots index)[lane.val].val : ZMod babyBearModulus) := by
  obtain ⟨c0, c1, c2, cs⟩ := control_entries w
  obtain ⟨s0, ss⟩ := slot_entries w
  obtain ⟨index, kind, e0, e2, flags⟩ := ThetaRho.SetupProofs.control_table_sound
    (row_sound h _) (control_tag w) (c1.trans active)
  rw [c0] at e0
  rw [c2] at e2
  have key : (row w 0)[0] = ((controlAt index.val + 2048 : Nat) : ZMod babyBearModulus) := by
    rw [s0, active, e0]; push_cast; ring
  have slots := ThetaRho.SetupProofs.slot_table_sound (row_sound h 0) (slot_tag w) index key
  refine ⟨index, kind, e0, e2, fun c => ?_, fun lane => ?_⟩
  · rw [← cs c]; exact flags c
  · rw [← ss lane]; exact slots lane

/-- D-byte XOR query `d`. -/
theorem xor_facts {w : Nat → ZMod babyBearModulus} (h : Holds w) (d : Fin 8) :
    (row w ⟨1 + d.val, by omega⟩)[0].val < 256 ∧ (row w ⟨1 + d.val, by omega⟩)[1].val < 256 ∧
      (row w ⟨1 + d.val, by omega⟩)[2].val < 256 ∧
      (row w ⟨1 + d.val, by omega⟩)[2].val =
        (row w ⟨1 + d.val, by omega⟩)[0].val ^^^ (row w ⟨1 + d.val, by omega⟩)[1].val := by
  obtain ⟨a, b, c, e, -⟩ := ThetaRho.SetupProofs.xor_byte_table_sound (row_sound h _) (xor_tag w d)
  exact ⟨a, b, c, e⟩

/-- XOR-and-split query `i`: both fragments of the XOR rotated by the shift. -/
theorem split_facts {w : Nat → ZMod babyBearModulus} (h : Holds w) (i : Fin 40) :
    (row w ⟨10 + i.val, by omega⟩)[0].val < 256 ∧ (row w ⟨10 + i.val, by omega⟩)[1].val < 256 ∧
      (row w ⟨10 + i.val, by omega⟩)[2].val < 8 ∧
      (row w ⟨10 + i.val, by omega⟩)[3].val < 256 ∧ (row w ⟨10 + i.val, by omega⟩)[4].val < 256 ∧
      (row w ⟨10 + i.val, by omega⟩)[3].val = ((row w ⟨10 + i.val, by omega⟩)[0].val ^^^
        (row w ⟨10 + i.val, by omega⟩)[1].val) * 2 ^ (row w ⟨10 + i.val, by omega⟩)[2].val % 256 ∧
      (row w ⟨10 + i.val, by omega⟩)[4].val = ((row w ⟨10 + i.val, by omega⟩)[0].val ^^^
        (row w ⟨10 + i.val, by omega⟩)[1].val) / 2 ^ (8 - (row w ⟨10 + i.val, by omega⟩)[2].val) := by
  obtain ⟨a, b, c, d, e, f, g, -⟩ :=
    ThetaRho.SetupProofs.split_table_sound (row_sound h _) (split_tag w i)
  exact ⟨a, b, c, d, e, f, g⟩

end Airbender.Keccak.Split.ThetaRho.Proofs

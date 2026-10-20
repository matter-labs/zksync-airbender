import Human.Circuits.WordMemory.Artifact
import Slop.WordMemory.ArtifactChecks
import Human.Helpers.Properties
import Slop.Arithmetic.Word
import Slop.Constraints
import Mathlib.Tactic.FinCases

namespace Airbender.WordMemory.Proofs
open Airbender.Arithmetic

/-- Execute/store/ROM flags, address carries and timestamp borrows. -/
theorem local_flags {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom)) :
    ∀ i : Fin 8, w (#v[4, 10, 35, 33, 34, 46, 47, 48][i]) = 0 ∨
      w (#v[4, 10, 35, 33, 34, 46, 47, 48][i]) = 1 := by
  intro i
  have flag := Verification.assertion_of_holds h
    ⟨(#v[0, 22, 23, 5, 6, 24, 25, 26][i]), by rw [constraint_count]; fin_cases i <;> decide⟩
  fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] at flag ⊢
  all_goals first | exact flag | exact flag.imp id Eq.symm

/-- Range queries cover the ROM separator residue and both final-PC limbs. -/
theorem local_ranges {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom)) :
    (w 36).val < limbBase ∧ (w 11).val < limbBase ∧ (w 12).val < limbBase := by
  have a := Verification.range16_bound (Verification.lookup_of_holds h ⟨0, by rw [lookup_count]; decide⟩)
  have b := Verification.range16_bound (Verification.lookup_of_holds h ⟨1, by rw [lookup_count]; decide⟩)
  have c := Verification.range16_bound (Verification.lookup_of_holds h ⟨2, by rw [lookup_count]; decide⟩)
  simpa [Expression.eval, Verification.environment] using And.intro a (And.intro b c)

/-- Final-PC bounds follow from the imported lookups; initial bounds remain explicit. -/
theorem pc_successor {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {rom : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (mapping : w 0 = (initial.lo : ZMod p) ∧ w 1 = (initial.hi : ZMod p) ∧
      final.lo = (w 11).val ∧ final.hi = (w 12).val)
    (initialBound : initial.Bounded) :
    final.value = initial.value + 4 ∧ initial.value + 4 < wordModulus ∧
      final.toBitVec = initial.toBitVec + 4 := by
  have carry := Verification.assertion_of_holds h ⟨18, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨19, by rw [constraint_count]; decide⟩
  have finalLo : w 11 = (final.lo : ZMod p) := by
    rw [mapping.2.2.1]; exact (ZMod.natCast_zmod_val _).symm
  have finalHi : w 12 = (final.hi : ZMod p) := by
    rw [mapping.2.2.2]; exact (ZMod.natCast_zmod_val _).symm
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mapping.1, mapping.2.1, finalLo, finalHi] at carry high
  let x : ZMod p := -30720 * (initial.lo + 4 - final.lo)
  have boolean : x * (x - 1) = 0 := by
    simpa [x, mul_eq_zero, sub_eq_add_neg] using carry
  have normalized : x + initial.hi - final.hi = 0 := by
    convert high using 1
    dsimp [x]
    ring
  obtain ⟨c, cb, low, hi⟩ := increment_carry inverse boolean normalized
  have ranges := local_ranges h
  have finalBound : final.Bounded :=
    ⟨mapping.2.2.1 ▸ ranges.2.1, mapping.2.2.2 ▸ ranges.2.2⟩
  exact Word.increment_of_limbs (by omega) (by decide) cb initialBound finalBound low hi

/-- The selected RAM address is rs1 plus the preprocessed immediate, modulo 2^32.
    Source, immediate and memory-address bounds remain explicit interfaces. -/
theorem effective_address {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {rom : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} (store : Bool)
    {source immediate address : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = if store then 1 else 0)
    (mapping : w 17 = (source.lo : ZMod p) ∧ w 18 = (source.hi : ZMod p) ∧
      w 8 = (immediate.lo : ZMod p) ∧ w 9 = (immediate.hi : ZMod p) ∧
      (if store then w 25 else w 19) = (address.lo : ZMod p) ∧
      (if store then w 26 else w 20) = (address.hi : ZMod p))
    (sourceBound : source.Bounded) (immediateBound : immediate.Bounded)
    (addressBound : address.Bounded) :
    address.toBitVec = source.toBitVec + immediate.toBitVec := by
  have low := Verification.assertion_of_holds h ⟨3, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have lo := mapping.2.2.2.2.1
  have hi := mapping.2.2.2.2.2
  cases store <;> simp only [Bool.false_eq_true, if_false, if_true] at selected lo hi
  all_goals
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected, mapping.1, mapping.2.1,
      mapping.2.2.1, mapping.2.2.2.1, lo, hi] at low high
    have defined : w 33 = -30720 * (source.lo + immediate.lo - address.lo) := by
      linear_combination low
    have highDefined : w 34 = -30720 * (w 33 + source.hi + immediate.hi - address.hi) := by
      rw [defined]
      linear_combination high
    have carryField : (source.lo : ZMod p) + immediate.lo = address.lo + 65536 * w 33 := by
      rw [defined]
      linear_combination -(source.lo + immediate.lo - address.lo) * inverse
    have wrapField : w 33 + source.hi + immediate.hi = address.hi + 65536 * w 34 := by
      rw [highDefined]
      linear_combination -(w 33 + source.hi + immediate.hi - address.hi) * inverse
    have cb : (w 33).val ≤ 1 := by simpa using boolean_val (local_flags h 3)
    have wb : (w 34).val ≤ 1 := by simpa using boolean_val (local_flags h 4)
    have result := Word.add_of_limbs hp sourceBound (right := ⟨0, 0⟩)
      (by exact ⟨by decide, by decide⟩) immediateBound addressBound (Nat.le_trans cb (by decide)) (Nat.le_trans wb (by decide))
      (by simpa using carryField) (by simpa using wrapField)
    simpa [Word.toBitVec, Word.value] using result

/-- The non-memory port addresses the decoded rs2 on SW and rd on LW. -/
theorem register_address {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p} (store : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = if store then 1 else 0) :
    (if store then w 19 else w 25) = (if store then w 6 else w 7) ∧
      (if store then w 20 else w 26) = 0 := by
  have lo := Verification.assertion_of_holds h ⟨1, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨2, by rw [constraint_count]; decide⟩
  cases store <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected] at lo hi ⊢
  all_goals constructor <;> first | linear_combination lo | exact hi

/-- The ranged subtraction classifies the selected address, and forbids ROM stores. -/
theorem rom_selection {p : Nat} [Fact p.Prime] (hp : 131072 < p)
    {rom : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} (store : Bool) {address : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = if store then 1 else 0)
    (mapping : (if store then w 26 else w 20) = (address.hi : ZMod p))
    (addressBound : address.Bounded) :
    w 35 = (if address.hi < 64 then 1 else 0) ∧
      (store = true → 64 ≤ address.hi) := by
  have definition := Verification.assertion_of_holds h ⟨7, by rw [constraint_count]; decide⟩
  have trap := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  -- The memory port is read on LW and written on SW.
  have residue : w 36 = 65536 * w 35 + address.hi - 64 := by
    cases store <;>
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, selected] at definition mapping
    all_goals rw [mapping] at definition; linear_combination definition
  have forbid : store = true → w 35 = 0 := by
    intro hs
    subst store
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected] using trap
  have flag : w 35 = (if address.hi < 64 then 1 else 0) :=
    range_separator hp (by simpa [limbBase] using addressBound.2) (by decide)
      (by simpa [limbBase] using (local_ranges h).1) (by simpa using local_flags h 2)
      (by linear_combination residue)
  refine ⟨flag, ?_⟩
  intro hs
  by_contra inside
  have inROM : address.hi < 64 := by omega
  have contradiction : (1 : ZMod p) = 0 := by simpa [flag, inROM] using forbid hs
  exact one_ne_zero contradiction

/-- Eliminate the copied intermediates in the imported nine-column ROM query.
    Table membership itself is Clean's; its program/setup binding is external. -/
theorem data_lookup {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p} (store : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = if store then 1 else 0) :
    rom.Contains #[] #v[
      w 35 * ((if store then w 25 else w 19) + 65536 * (if store then w 26 else w 20)),
      w 31 - (1 - w 35) * w 23, w 32 - (1 - w 35) * w 24,
      0, 0, 0, 0, 0, w 4 * w 35 * 34] := by
  have r := Verification.assertion_of_holds h ⟨9, by rw [constraint_count]; decide⟩
  have address := Verification.assertion_of_holds h ⟨10, by rw [constraint_count]; decide⟩
  have key := Verification.assertion_of_holds h ⟨11, by rw [constraint_count]; decide⟩
  have lo := Verification.assertion_of_holds h ⟨12, by rw [constraint_count]; decide⟩
  have loCopy := Verification.assertion_of_holds h ⟨13, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨14, by rw [constraint_count]; decide⟩
  have hiCopy := Verification.assertion_of_holds h ⟨15, by rw [constraint_count]; decide⟩
  have active := Verification.assertion_of_holds h ⟨16, by rw [constraint_count]; decide⟩
  have tag := Verification.assertion_of_holds h ⟨17, by rw [constraint_count]; decide⟩
  have query := Verification.lookup_of_holds h ⟨3, by rw [lookup_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at r address key lo loCopy hi hiCopy active tag
  have rEq : w 37 = w 35 := by linear_combination r
  have loEq : w 41 = w 31 - (1 - w 35) * w 23 := by linear_combination lo + loCopy
  have hiEq : w 43 = w 32 - (1 - w 35) * w 24 := by linear_combination hi + hiCopy
  have activeEq : w 44 = w 4 := by linear_combination active
  have tagEq : w 45 = w 4 * w 35 * 34 := by
    rw [rEq, activeEq] at tag
    linear_combination tag
  have keyEq : w 39 = w 35 * ((if store then w 25 else w 19) +
      65536 * (if store then w 26 else w 20)) := by
    cases store <;> simp only [Bool.false_eq_true, if_false, if_true] at selected ⊢
    all_goals
      simp only [selected, rEq] at address key
      linear_combination key + w 35 * address
  simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, Table.toRaw,
    Verification.environment, Expression.eval, fromElements, keyEq, loEq, hiEq, tagEq] using query

/-- The zero-tag table row forces RAM loads and stores to copy both data limbs.
    The premise describes every disabled table row, not the circuit's result. -/
theorem ram_data {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    (zeroRows : ∀ row, rom.Contains #[] row → row[8] = 0 → row[1] = 0 ∧ row[2] = 0)
    {w : Nat → ZMod p} (store : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = if store then 1 else 0) (ram : w 35 = 0) :
    w 31 = w 23 ∧ w 32 = w 24 := by
  have query := data_lookup store h selected
  simp only [ram, mul_zero, zero_mul, sub_zero, one_mul] at query
  have values := zeroRows _ query rfl
  simpa [sub_eq_zero] using values

/-- An active ROM load queries the selected address and the written data directly. -/
theorem rom_data {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = 0) (active : w 4 = 1) (inROM : w 35 = 1) :
    rom.Contains #[] #v[w 19 + 65536 * w 20, w 31, w 32, 0, 0, 0, 0, 0, 34] := by
  have query := data_lookup false h selected
  simpa [inROM, active] using query

end Airbender.WordMemory.Proofs

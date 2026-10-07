import Airbender.Proofs.SubwordMemory.Lookups
import Airbender.Review.SubwordMemory.Artifact
import Airbender.Review.Properties
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Constraints
import Mathlib.Tactic.FinCases

namespace Airbender.SubwordMemory.Proofs
open Airbender.Arithmetic

/-- Execute/selectors, offset bits, address carries, ROM flag and timestamp borrows. -/
theorem local_flags {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ i : Fin 12, w (#v[4, 10, 11, 12, 35, 36, 37, 38, 41, 62, 63, 64][i]) = 0 ∨
      w (#v[4, 10, 11, 12, 35, 36, 37, 38, 41, 62, 63, 64][i]) = 1 := by
  intro i
  have flag := Verification.assertion_of_holds h
    ⟨(#v[0, 34, 35, 36, 37, 38, 4, 6, 39, 40, 41, 42][i]), by rw [constraint_count]; fin_cases i <;> decide⟩
  fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] at flag ⊢
  all_goals first | exact flag | exact flag.imp id Eq.symm

/-- All five imported ranges: aligned low address, word-cell index, ROM residue and PC. -/
theorem local_ranges {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w 39).val < limbBase ∧ (w 40).val < limbBase ∧ (w 42).val < limbBase ∧
      (w 13).val < limbBase ∧ (w 14).val < limbBase := by
  have a := Verification.range16_bound (Verification.lookup_of_holds h ⟨0, by rw [lookup_count]; decide⟩)
  have b := Verification.range16_bound (Verification.lookup_of_holds h ⟨1, by rw [lookup_count]; decide⟩)
  have c := Verification.range16_bound (Verification.lookup_of_holds h ⟨2, by rw [lookup_count]; decide⟩)
  have d := Verification.range16_bound (Verification.lookup_of_holds h ⟨3, by rw [lookup_count]; decide⟩)
  have e := Verification.range16_bound (Verification.lookup_of_holds h ⟨4, by rw [lookup_count]; decide⟩)
  simpa [Expression.eval, Verification.environment] using
    And.intro a (And.intro b (And.intro c (And.intro d e)))

/-- Final-PC bounds follow fsetup the imported lookups; initial bounds remain explicit. -/
theorem pc_successor {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mapping : w 0 = (initial.lo : ZMod p) ∧ w 1 = (initial.hi : ZMod p) ∧
      final.lo = (w 13).val ∧ final.hi = (w 14).val)
    (initialBound : initial.Bounded) :
    final.value = initial.value + 4 ∧ initial.value + 4 < wordModulus ∧
      final.toBitVec = initial.toBitVec + 4 := by
  have carry := Verification.assertion_of_holds h ⟨30, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨31, by rw [constraint_count]; decide⟩
  have finalLo : w 13 = (final.lo : ZMod p) := by
    rw [mapping.2.2.1]; exact (ZMod.natCast_zmod_val _).symm
  have finalHi : w 14 = (final.hi : ZMod p) := by
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
    ⟨mapping.2.2.1 ▸ ranges.2.2.2.1, mapping.2.2.2 ▸ ranges.2.2.2.2⟩
  exact Word.increment_of_limbs (by omega) (by decide) cb initialBound finalBound low hi


/-- The opposite port selects rs2 on stores and rd on loads. -/
theorem register_address {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p} (store : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 10 = if store then 1 else 0) :
    (if store then w 21 else w 27) = (if store then w 6 else w 7) ∧
      (if store then w 22 else w 28) = 0 := by
  have lo := Verification.assertion_of_holds h ⟨1, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨2, by rw [constraint_count]; decide⟩
  cases store <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected] at lo hi ⊢
  all_goals constructor <;> first | linear_combination lo | exact hi

/-- The local queries force a canonical, word-aligned low address. -/
theorem aligned_address {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} (store : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 10 = if store then 1 else 0) :
    (if store then w 27 else w 21) = w 39 ∧
      (w 39).val < limbBase ∧ (w 39).val % 4 = 0 := by
  have copy := Verification.assertion_of_holds h ⟨7, by rw [constraint_count]; decide⟩
  have aligned := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  have copied : (if store then w 27 else w 21) = w 39 := by
    cases store <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected] at copy ⊢
    all_goals linear_combination -copy
  have field : w 39 = 4 * w 40 := by
    cases store <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected] at aligned copied
    all_goals rw [copied] at aligned; linear_combination aligned
  have ranges := local_ranges h
  have low := ranges.1
  have quotient := ranges.2.1
  unfold limbBase at low quotient
  have natural : (w 39).val = 4 * (w 40).val :=
    bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using field)
  exact ⟨copied, low, by omega⟩

/-- Halfword selection rejects an odd byte offset, using the imported trap equation. -/
theorem halfword_aligned {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (halfword : w 11 = 0) : w 35 = 0 := by
  have trap := Verification.assertion_of_holds h ⟨9, by rw [constraint_count]; decide⟩
  simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, halfword] using trap

/-- Address addition recovers the word cell and its unique byte offset. The
    selected high address remains a memory-interface bound; the low bound is local. -/
theorem effective_address {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} (store : Bool)
    {source immediate cell : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 10 = if store then 1 else 0)
    (mapping : w 19 = (source.lo : ZMod p) ∧ w 20 = (source.hi : ZMod p) ∧
      w 8 = (immediate.lo : ZMod p) ∧ w 9 = (immediate.hi : ZMod p) ∧
      cell.lo = (if store then w 27 else w 21).val ∧
      (if store then w 28 else w 22) = (cell.hi : ZMod p))
    (sourceBound : source.Bounded) (immediateBound : immediate.Bounded)
    (highBound : cell.hi < limbBase) :
    let offset := (w 35).val + 2 * (w 36).val
    cell.Bounded ∧ cell.value % 4 = 0 ∧ offset < 4 ∧
      cell.toBitVec + BitVec.ofNat 32 offset = source.toBitVec + immediate.toBitVec ∧
      (source.toBitVec + immediate.toBitVec).toNat % 4 = offset := by
  dsimp only
  have aligned := aligned_address hp store h selected
  have lo : (if store then w 27 else w 21) = (cell.lo : ZMod p) := by
    rw [mapping.2.2.2.2.1]
    exact (ZMod.natCast_zmod_val _).symm
  have cellLo : cell.lo = (w 39).val := by rw [mapping.2.2.2.2.1, aligned.1]
  have bounded : cell.Bounded := ⟨cellLo ▸ aligned.2.1, highBound⟩
  have cellAligned : cell.lo % 4 = 0 := cellLo ▸ aligned.2.2
  have bit0 := boolean_val (local_flags h 4)
  have bit1 := boolean_val (local_flags h 5)
  have cb := boolean_val (local_flags h 6)
  have wb := boolean_val (local_flags h 7)
  dsimp at bit0 bit1 cb wb
  have offsetBound : (w 35).val + 2 * (w 36).val < 4 := by omega
  have fullBound : (Word.mk (cell.lo + (w 35).val + 2 * (w 36).val) cell.hi).Bounded := by
    constructor
    · change cell.lo + (w 35).val + 2 * (w 36).val < limbBase
      have lowBound := bounded.1
      unfold limbBase at *
      omega
    · exact highBound
  have low := Verification.assertion_of_holds h ⟨3, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  have hi := mapping.2.2.2.2.2
  have lowField : (source.lo : ZMod p) + immediate.lo =
      cell.lo + w 35 + 2 * w 36 + 65536 * w 37 := by
    cases store <;> simp only [Bool.false_eq_true, if_false, if_true] at selected lo hi
    all_goals
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, selected, mapping.1, mapping.2.2.1, lo] at low
      linear_combination -(source.lo + immediate.lo - cell.lo - w 35 - 2 * w 36) * inverse - 65536 * low
  have highField : w 37 + (source.hi : ZMod p) + immediate.hi = cell.hi + 65536 * w 38 := by
    cases store <;> simp only [Bool.false_eq_true, if_false, if_true] at selected lo hi
    all_goals
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, selected, mapping.1, mapping.2.1,
        mapping.2.2.1, mapping.2.2.2.1, lo, hi] at low high
      have normalized : w 38 = -30720 * (w 37 + source.hi + immediate.hi - cell.hi) := by
        linear_combination high + 30720 * low
      linear_combination -(w 37 + source.hi + immediate.hi - cell.hi) * inverse - 65536 * normalized
  have result := Word.add_of_limbs (by omega : 196608 < p) sourceBound (right := ⟨0, 0⟩)
    (by exact ⟨by decide, by decide⟩) immediateBound fullBound (Nat.le_trans cb (by decide)) (Nat.le_trans wb (by decide))
    (by simpa [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, add_assoc] using lowField)
    (by simpa [ZMod.natCast_zmod_val] using highField)
  have assembled : (Word.mk (cell.lo + (w 35).val + 2 * (w 36).val) cell.hi).toBitVec =
      cell.toBitVec + BitVec.ofNat 32 ((w 35).val + 2 * (w 36).val) := by
    unfold Word.toBitVec
    rw [← BitVec.ofNat_add]
    congr 1
    simp only [Word.value]
    omega
  have alignedValue : cell.value % 4 = 0 := by
    unfold Word.value limbBase
    omega
  refine ⟨bounded, alignedValue, offsetBound, assembled.symm.trans ?_, ?_⟩
  · simpa [Word.toBitVec, Word.value] using result
  · have fullValue := Word.toBitVec_toNat fullBound
    have equal : source.toBitVec + immediate.toBitVec =
        (Word.mk (cell.lo + (w 35).val + 2 * (w 36).val) cell.hi).toBitVec := by
      simpa [Word.toBitVec, Word.value] using result.symm
    rw [equal, fullValue]
    unfold Word.value limbBase
    dsimp only
    omega

/-- The ranged subtraction classifies the selected address, and forbids ROM stores. -/
theorem rom_selection {p : Nat} [Fact p.Prime] (hp : 131072 < p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} (store : Bool) {address : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 10 = if store then 1 else 0)
    (mapping : (if store then w 28 else w 22) = (address.hi : ZMod p))
    (addressBound : address.Bounded) :
    w 41 = (if address.hi < 64 then 1 else 0) ∧
      (store = true → 64 ≤ address.hi) := by
  have definition := Verification.assertion_of_holds h ⟨10, by rw [constraint_count]; decide⟩
  have trap := Verification.assertion_of_holds h ⟨11, by rw [constraint_count]; decide⟩
  -- The memory port is read on LW and written on SW.
  have residue : w 42 = 65536 * w 41 + address.hi - 64 := by
    cases store <;>
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, selected] at definition mapping
    all_goals rw [mapping] at definition; linear_combination definition
  have forbid : store = true → w 41 = 0 := by
    intro hs
    subst store
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected] using trap
  have ranges := local_ranges h
  have flag : w 41 = (if address.hi < 64 then 1 else 0) :=
    range_separator hp (by simpa [limbBase] using addressBound.2) (by decide)
      (by simpa [limbBase] using ranges.2.2.1) (by simpa using local_flags h 8)
      (by linear_combination residue)
  refine ⟨flag, ?_⟩
  intro hs
  by_contra inside
  have inROM : address.hi < 64 := by omega
  have contradiction : (1 : ZMod p) = 0 := by simpa [flag, inROM] using forbid hs
  exact one_ne_zero contradiction

/-- The unconditional byte-clearing query, with its copied intermediates removed. -/
theorem clearing_query {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    setup.Contains #[] #v[w 36 * w 32 + (1 - w 36) * w 31 + 65536 * w 35,
      w 43, 0, 0, 0, 0, 0, 0, 30] := by
  have input := Verification.assertion_of_holds h ⟨12, by rw [constraint_count]; decide⟩
  have output := Verification.assertion_of_holds h ⟨13, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at input output
  have inputEq : w 44 = w 36 * w 32 + (1 - w 36) * w 31 + 65536 * w 35 := by
    linear_combination input
  have outputEq : w 45 = w 43 := by linear_combination output
  have query := Verification.lookup_of_holds h ⟨5, by rw [lookup_count]; decide⟩
  simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, Table.toRaw, fromElements, Expression.eval,
    Verification.environment, inputEq, outputEq] using query

/-- The shared data query, after eliminating copied selectors and result limbs.
    Branch-specific key/keep definitions are unfolded by the following lemmas. -/
theorem data_query {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    setup.Contains #[] #v[w 41 * w 49 + (1 - w 10 - w 41) * w 50 + w 10 * w 51,
      (1 - w 10) * w 33 + w 10 * w 54, (1 - w 10) * w 34 + w 10 * w 57,
      0, 0, 0, 0, 0,
      w 4 * (w 41 * (1 - w 11) * 44 + w 41 * w 11 * 45 +
        (1 - w 10 - w 41) * (1 - w 11) * 42 + (1 - w 10 - w 41) * w 11 * 43 +
        w 10 * w 11 * 29)] := by
  have r := Verification.assertion_of_holds h ⟨14, by rw [constraint_count]; decide⟩
  have a := Verification.assertion_of_holds h ⟨15, by rw [constraint_count]; decide⟩
  have s := Verification.assertion_of_holds h ⟨16, by rw [constraint_count]; decide⟩
  have input := Verification.assertion_of_holds h ⟨20, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds h ⟨21, by rw [constraint_count]; decide⟩
  have outLow := Verification.assertion_of_holds h ⟨23, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨24, by rw [constraint_count]; decide⟩
  have outHigh := Verification.assertion_of_holds h ⟨26, by rw [constraint_count]; decide⟩
  have tag := Verification.assertion_of_holds h ⟨27, by rw [constraint_count]; decide⟩
  have enabled := Verification.assertion_of_holds h ⟨28, by rw [constraint_count]; decide⟩
  have outTag := Verification.assertion_of_holds h ⟨29, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at r a s input low outLow high outHigh tag enabled outTag
  have romEq : w 46 = w 41 := by linear_combination r
  have ramEq : w 47 = 1 - w 10 - w 41 := by linear_combination a
  have storeEq : w 48 = w 10 := by linear_combination s
  have enabledEq : w 60 = w 4 := by linear_combination enabled
  rw [romEq, ramEq, storeEq] at input outLow outHigh
  rw [enabledEq] at outTag
  have keyEq : w 52 = w 41 * w 49 + (1 - w 10 - w 41) * w 50 + w 10 * w 51 := by
    linear_combination input
  have lowEq : w 55 = (1 - w 10) * w 33 + w 10 * w 54 := by
    linear_combination (1 - w 10) * low + outLow
  have highEq : w 58 = (1 - w 10) * w 34 + w 10 * w 57 := by
    linear_combination (1 - w 10) * high + outHigh
  have tagEq : w 61 = w 4 * (w 41 * (1 - w 11) * 44 + w 41 * w 11 * 45 +
      (1 - w 10 - w 41) * (1 - w 11) * 42 + (1 - w 10 - w 41) * w 11 * 43 +
      w 10 * w 11 * 29) := by linear_combination w 4 * tag + outTag
  have query := Verification.lookup_of_holds h ⟨6, by rw [lookup_count]; decide⟩
  simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, Table.toRaw, fromElements,
    Expression.eval, Verification.environment, keyEq, lowEq, highEq, tagEq] using query

/-- A RAM load selects the read halfword. Tags 42/43 are the Rust
    halfword/byte sign-extension tables. -/
theorem ram_load_query {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) (load : w 10 = 0) (ram : w 41 = 0) :
    setup.Contains #[] #v[w 36 * w 26 + (1 - w 36) * w 25 + 65536 * w 12 + 131072 * w 35,
      w 33, w 34, 0, 0, 0, 0, 0, (1 - w 11) * 42 + w 11 * 43] := by
  have key := Verification.assertion_of_holds h ⟨18, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at key
  have keyEq : w 50 = w 36 * w 26 + (1 - w 36) * w 25 + 65536 * w 12 + 131072 * w 35 := by
    linear_combination key
  simpa [active, load, ram, keyEq] using data_query h

/-- ROM loads use an address/sign/offset key, not the RAM read-port placeholder. -/
theorem rom_load_query {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) (load : w 10 = 0) (rom : w 41 = 1) :
    setup.Contains #[] #v[w 21 + 65536 * w 22 + 4194304 * w 12 + 8388608 * w 36 + 16777216 * w 35,
      w 33, w 34, 0, 0, 0, 0, 0, (1 - w 11) * 44 + w 11 * 45] := by
  have key := Verification.assertion_of_holds h ⟨17, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, load] at key
  have keyEq : w 49 = w 21 + 65536 * w 22 + 4194304 * w 12 + 8388608 * w 36 + 16777216 * w 35 := by
    linear_combination key
  simpa [active, load, rom, keyEq] using data_query h

/-- Stores preserve the untouched halfword and constrain the changed halfword
    through the source-byte table (SB) or zero table (SH). -/
theorem store_query {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) (store : w 10 = 1) (ram : w 41 = 0) :
    setup.Contains #[] #v[w 11 * (w 25 + 65536 * w 35),
      w 36 * w 34 + (1 - w 36) * w 33 - w 11 * w 43 - (1 - w 11) * w 25,
      w 36 * (w 33 - w 31) + (1 - w 36) * (w 34 - w 32),
      0, 0, 0, 0, 0, w 11 * 29] := by
  have key := Verification.assertion_of_holds h ⟨19, by rw [constraint_count]; decide⟩
  have keep := Verification.assertion_of_holds h ⟨22, by rw [constraint_count]; decide⟩
  have other := Verification.assertion_of_holds h ⟨25, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at key keep other
  have keyEq : w 51 = w 11 * (w 25 + 65536 * w 35) := by linear_combination key
  have keepEq : w 54 = w 36 * w 34 + (1 - w 36) * w 33 - w 11 * w 43 - (1 - w 11) * w 25 := by
    linear_combination keep
  have otherEq : w 57 = w 36 * (w 33 - w 31) + (1 - w 36) * (w 34 - w 32) := by
    linear_combination other
  simpa [active, store, ram, keyEq, keepEq, otherEq] using data_query h

/-- Both RAM-load modes derive result-limb bounds from the fixed setup table.
    No output-range assumption or witness-generation premise is needed. -/
theorem ram_output_bounds {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    {program : Nat → BitVec 32} {w : Nat → ZMod p} (byte : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (Verification.subwordTable program)))
    (active : w 4 = 1) (load : w 10 = 0) (ram : w 41 = 0)
    (selected : w 11 = if byte then 1 else 0) :
    (Word.mk (w 33).val (w 34).val).Bounded := by
  have query := ram_load_query h active load ram
  have tag : ((1 - w 11) * 42 + w 11 * 43) = ((if byte then 43 else 42 : Nat) : ZMod p) := by
    cases byte <;> simp [selected]
  have extended := Verification.subword_ram_extension hp byte query tag
  exact extended.1

end Airbender.SubwordMemory.Proofs

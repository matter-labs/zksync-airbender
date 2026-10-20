import Slop.WordMemory
import Slop.BabyBear
import Slop.Sail.Memory
import Mathlib.Tactic.IntervalCases

namespace Tests.WordMemory
open Airbender
open Airbender.Arithmetic

-- RAM-only rows use the real setup's disabled-ROM zero query. This small fixture
-- supplies that row; it makes no assertion about a ROM image or global memory.
private def zeroTable : Table (ZMod babyBearModulus) (fields 9) := .fromStatic {
  name := "DisabledROMFixture"
  length := 1
  row _ := Vector.replicate 9 0
  index _ := 0
  Spec x := ∃ i : Fin 1, x = (fun (_ : Fin 1) => Vector.replicate 9 0) i
  contains_iff _ := Iff.rfl
}

private def row (store : Bool) : Nat → ZMod babyBearModulus
  | 0 | 17 => 65532
  | 4 | 5 | 12 | 33 | 36 | 44 => 1
  | 6 => if store then 2 else 0
  | 7 | 25 => if store then 0 else 1
  | 8 | 13 => 4
  | 10 => if store then 1 else 0
  | 18 => 64
  | 19 => if store then 2 else 0
  | 20 => if store then 0 else 65
  | 23 | 31 => 1234
  | 24 | 32 => 5678
  | 26 => if store then 65 else 0
  | 38 => 4259840
  | _ => 0

set_option maxRecDepth 4096 in
private theorem satisfies (store : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row store))
      (WordMemory.importedConstraints zeroTable) := by
  cases store <;>
    simp [WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, row, Lookup.Contains,
      zeroTable, Table.fromStatic, Table.toRaw]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)
    | exact ⟨0, rfl⟩

-- Both actual load/store rows cross a limb boundary in address and PC arithmetic.
example (store : Bool) :
    (Word.mk 0 65).toBitVec = (Word.mk 65532 64).toBitVec + (Word.mk 4 0).toBitVec := by
  apply WordMemory.Proofs.effective_address (p := babyBearModulus) (by decide) (by decide)
    store (satisfies store)
  · cases store <;> rfl
  · cases store <;> norm_num [row]
  all_goals exact ⟨by decide, by decide⟩

example (store : Bool) :
    (Word.mk 0 1).value = (Word.mk 65532 0).value + 4 := by
  exact (WordMemory.Proofs.pc_successor (p := babyBearModulus) (by decide) (by decide)
    (satisfies store) ⟨rfl, rfl, rfl, rfl⟩ ⟨by decide, by decide⟩).1

private theorem zero_outputs (entry : Vector (ZMod babyBearModulus) 9)
    (h : zeroTable.Contains #[] entry) (_tag : entry[8] = 0) :
    entry[1] = 0 ∧ entry[2] = 0 := by
  obtain ⟨i, rfl⟩ := h
  simp

example (store : Bool) :
    row store 31 = row store 23 ∧ row store 32 = row store 24 := by
  apply WordMemory.Proofs.ram_data zero_outputs store (satisfies store)
  · cases store <;> rfl
  · rfl

-- Changing either RAM data limb makes the imported relation unsatisfiable.
example {w : Nat → ZMod babyBearModulus} (store : Bool)
    (selected : w 10 = if store then 1 else 0) (ram : w 35 = 0)
    (wrong : w 31 ≠ w 23 ∨ w 32 ≠ w 24) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.importedConstraints zeroTable) := by
  intro h
  have equal := WordMemory.Proofs.ram_data zero_outputs store h selected ram
  rcases wrong with wrong | wrong
  · exact wrong equal.1
  · exact wrong equal.2

-- SW cannot target ROM, for any supplied table.
example {rom : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (selected : w 10 = 1) (romAddress : w 26 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.importedConstraints rom) := by
  intro h
  have outside := (WordMemory.Proofs.rom_selection (p := babyBearModulus) (by decide)
    true (address := ⟨0, 0⟩) h selected romAddress ⟨by decide, by decide⟩).2 rfl
  norm_num at outside

-- An independently supplied program fixture: zero row and one ROM word.
private def programTable : Table (ZMod babyBearModulus) (fields 9) := .fromStatic {
  name := "ROMWordFixture"
  length := 2
  row i := if i.val = 0 then Vector.replicate 9 0 else
    #v[65536, 1234, 5678, 0, 0, 0, 0, 0, 34]
  index entry := if entry[8] = 0 then 0 else 1
  Spec entry := ∃ i : Fin 2, entry = if i.val = 0 then Vector.replicate 9 0 else
    #v[65536, 1234, 5678, 0, 0, 0, 0, 0, 34]
  contains_iff _ := Iff.rfl
}

-- Independent native program bytes (little endian), rather than an output witness.
private def programState : Reference.RiscV.Sail.State := {
  regs := ∅
  mem := ((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 65536 210).insert 65537 4
    |>.insert 65538 46 |>.insert 65539 22
  tags := ()
  cycleCount := 0
  sailOutput := #[] }

-- This checks that the uniform ROM-image contract is inhabited for a nonempty
-- program table. Data columns are field elements decoded canonically.
example (address : Word) (lo hi : ZMod babyBearModulus)
    (bounded : address.Bounded) (inROM : address.hi < 64)
    (query : programTable.Contains #[] #v[(address.lo : ZMod babyBearModulus) +
      65536 * address.hi, lo, hi, 0, 0, 0, 0, 0, 34]) :
    _root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 address.toBitVec.toNat programState =
      .ok (Word.mk lo.val hi.val).toBitVec programState := by
  obtain ⟨i, member⟩ := query
  fin_cases i
  · have tag := congrArg (fun entry : Vector (ZMod babyBearModulus) 9 => entry[8]) member
    exact False.elim ((by decide : (34 : ZMod babyBearModulus) ≠ 0) tag)
  · have key := congrArg (fun entry : Vector (ZMod babyBearModulus) 9 => entry[0]) member
    have low := congrArg (fun entry : Vector (ZMod babyBearModulus) 9 => entry[1]) member
    have high := congrArg (fun entry : Vector (ZMod babyBearModulus) 9 => entry[2]) member
    change lo = 1234 at low
    change hi = 5678 at high
    have field : (address.value : ZMod babyBearModulus) = 65536 := by
      simpa [Word.value, limbBase] using key
    have natural : address.value = 65536 :=
      bounded_nat_eq (F := ZMod babyBearModulus) (p := babyBearModulus)
        (by have hb := bounded.1; unfold Word.value limbBase babyBearModulus at *; omega)
        (by decide) (by exact_mod_cast field)
    have addressValue : address.toBitVec.toNat = 65536 := by
      simp [Word.toBitVec, natural]
    rw [addressValue, low, high]
    simp only [_root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get,
      EStateM.pure]
    simp [programState, Std.ExtHashMap.getElem_insert, EStateM.pure]
    rfl

private def romRow : Nat → ZMod babyBearModulus
  | 0 | 17 => 65532
  | 4 | 5 | 7 | 12 | 20 | 25 | 33 | 35 | 37 | 44 => 1
  | 8 | 13 => 4
  | 23 => 99
  | 24 => 88
  | 31 | 40 | 41 => 1234
  | 32 | 42 | 43 => 5678
  | 36 => 65473
  | 38 | 39 => 65536
  | 45 => 34
  | _ => 0

set_option maxRecDepth 4096 in
private theorem rom_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment romRow)
      (WordMemory.importedConstraints programTable) := by
  simp [WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, romRow, Lookup.Contains,
    programTable, Table.fromStatic, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)
    | exact ⟨1, rfl⟩

example : romRow 35 = 1 :=
  (WordMemory.Proofs.rom_selection (p := babyBearModulus) (by decide)
    false (address := ⟨0, 1⟩) rom_satisfies rfl rfl ⟨by decide, by decide⟩).1

-- ROM data comes from the table, despite unrelated RAM-read placeholders.
example {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.importedConstraints programTable))
    (selected : w 10 = 0) (active : w 4 = 1) (inROM : w 35 = 1) :
    w 31 = 1234 ∧ w 32 = 5678 := by
  have query := WordMemory.Proofs.rom_data h selected active inROM
  obtain ⟨i, member⟩ := query
  fin_cases i
  · have tag := congrArg (fun entry : Vector (ZMod babyBearModulus) 9 => entry[8]) member
    exact False.elim ((by decide : (34 : ZMod babyBearModulus) ≠ 0) tag)
  · have low := congrArg (fun entry : Vector (ZMod babyBearModulus) 9 => entry[1]) member
    have high := congrArg (fun entry : Vector (ZMod babyBearModulus) 9 => entry[2]) member
    exact ⟨low, high⟩

end Tests.WordMemory

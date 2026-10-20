import Slop.SubwordMemory.Claims
import Slop.SubwordMemory.Stores
import Slop.BabyBear

namespace Tests.SubwordMemory
open Airbender Airbender.Arithmetic

-- Two independently fixed rows exercise the imported clearing and RAM-byte
-- queries. They are a boundary fixture, not a replacement setup table.
private def fixtureRow (i : Fin 2) : Vector (ZMod babyBearModulus) 9 :=
  if i.val = 0 then #v[65536, 0, 0, 0, 0, 0, 0, 0, 30]
  else #v[135732, 18, 0, 0, 0, 0, 0, 0, 43]

private def fixture : Table (ZMod babyBearModulus) (fields 9) := .fromStatic {
  name := "SubwordLoadFixture"
  length := 2
  row := fixtureRow
  index x := if x[8] = 30 then 0 else 1
  Spec x := ∃ i : Fin 2, x = fixtureRow i
  contains_iff _ := Iff.rfl
}

-- LBU at 0x00400001 reads byte 0x12 from the word 0x56781234.
def row : Nat → ZMod babyBearModulus
  | 4 | 5 | 11 | 19 | 35 | 47 | 60 => 1
  | 7 | 27 => 2
  | 13 | 15 => 4
  | 20 | 22 => 64
  | 25 => 4660
  | 26 => 22136
  | 33 | 53 | 54 | 55 => 18
  | 44 => 65536
  | 49 => 20971520
  | 50 | 52 => 135732
  | 51 => 70196
  | 59 | 61 => 43
  | _ => 0

set_option maxRecDepth 4096 in
private theorem satisfies_table (setup : Table (ZMod babyBearModulus) (fields 9))
    (members : ∀ i : Fin 2, setup.Contains #[] (fixtureRow i)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (SubwordMemory.importedConstraints setup) := by
  simp [SubwordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, row, Lookup.Contains,
    Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)
    | (simpa [fixtureRow] using members 0)
    | (simpa [fixtureRow] using members 1)

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (SubwordMemory.importedConstraints fixture) :=
  satisfies_table fixture (fun i => ⟨i, rfl⟩)

-- The same complete LBU witness also satisfies the full reconstructed setup.
theorem satisfies_setup :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (SubwordMemory.importedConstraints (Verification.subwordTable (fun _ => 0))) := by
  apply satisfies_table
  intro i
  fin_cases i
  · refine ⟨⟨196609, by decide⟩, ?_⟩
    norm_num [fixtureRow, Verification.subwordRow, Verification.subwordDataRow,
      Verification.subwordLoadLimbs, Verification.subwordStoreContribution]
  · refine ⟨⟨528949, by decide⟩, ?_⟩
    norm_num [fixtureRow, Verification.subwordRow, Verification.subwordDataRow,
      Verification.subwordLoadLimbs, Verification.subwordStoreContribution]

example : (Word.mk (row 33).val (row 34).val).Bounded :=
  SubwordMemory.Proofs.ram_output_bounds (p := babyBearModulus) (by decide) true
    satisfies_setup rfl rfl rfl rfl

-- The complete imported LBU row selects the second byte of its independently
-- fixed RAM word, not an unconstrained value supplied by the witness generator.
example : (Word.mk (row 33).val (row 34).val).toBitVec =
    SailRV32.Functions.extend_value true
      (((Word.mk 4660 22136).toBitVec >>> 8).setWidth 8) := by
  have data := SubwordMemory.Proofs.ram_load_data (p := babyBearModulus)
    (readData := ⟨4660, 22136⟩) (by decide) true false true false satisfies_setup
    rfl rfl rfl rfl rfl rfl rfl ⟨rfl, rfl⟩ ⟨by decide, by decide⟩ (by decide)
  exact data.2

private def nativeState : Reference.RiscV.Sail.State := {
  regs := {}
  mem := ({} : Std.ExtHashMap Nat (BitVec 8)).insert 4194304 52 |>.insert 4194305 18
    |>.insert 4194306 120 |>.insert 4194307 86
  tags := ()
  cycleCount := 0
  sailOutput := #[] }

private theorem nativeRead :
    _root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 4194304 nativeState =
      .ok (Word.mk 4660 22136).toBitVec nativeState := by
  simp only [_root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte, get, getThe,
    MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure]
  simp [nativeState, Std.ExtHashMap.getElem_insert, EStateM.pure]
  rfl

example (offset : Fin 4) :
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 1 (4194304 + offset.val)).run nativeState =
      .ok (((Word.mk 4660 22136).toBitVec >>> (8 * offset.val)).setWidth 8) nativeState :=
  Reference.RiscV.Sail.read_subword true offset.isLt (by simp) nativeRead

example (half : Fin 2) :
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 2 (4194304 + 2 * half.val)).run nativeState =
      .ok (((Word.mk 4660 22136).toBitVec >>> (8 * (2 * half.val))).setWidth 16) nativeState :=
  Reference.RiscV.Sail.read_subword false (by omega) (by intro _; omega) nativeRead

-- Sign-boundary checks use the same generic Sail-extension proof as table soundness.
example : SailRV32.Functions.extend_value false (BitVec.ofNat 8 128) = (Word.mk 65408 65535).toBitVec := by
  exact (Verification.extend_subword_limbs true true 128 (by decide)).2.symm

example : SailRV32.Functions.extend_value false (BitVec.ofNat 16 32768) = (Word.mk 32768 65535).toBitVec := by
  exact (Verification.extend_subword_limbs false true 32768 (by decide)).2.symm

example : (Word.mk 0 64).toBitVec + 1 = (Word.mk 1 64).toBitVec + (Word.mk 0 0).toBitVec := by
  have address := SubwordMemory.Proofs.effective_address (p := babyBearModulus)
    (source := ⟨1, 64⟩) (immediate := ⟨0, 0⟩) (cell := ⟨0, 64⟩)
    (by decide) (by decide) false satisfies rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide)
  simpa [row, show (1 : ZMod babyBearModulus).val = 1 from by decide,
    show (0 : ZMod babyBearModulus).val = 0 from by decide] using address.2.2.2.1

-- A satisfying halfword row cannot use an odd address offset.
example {setup : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (halfword : w 11 = 0) (odd : w 35 ≠ 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (SubwordMemory.importedConstraints setup) := by
  intro h
  exact odd (SubwordMemory.Proofs.halfword_aligned h halfword)

-- Neither cell alignment nor the offset decomposition is a witness-generator assumption.
example {setup : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (load : w 10 = 0) (misaligned : (w 21).val % 4 ≠ 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (SubwordMemory.importedConstraints setup) := by
  intro h
  have aligned := SubwordMemory.Proofs.aligned_address (p := babyBearModulus) (by decide) false h load
  exact misaligned (by simpa [← aligned.1] using aligned.2.2)

-- SB at byte offset one and SH at halfword offset two share the same old cell.
private def storeRow (byte : Bool) : Nat → ZMod babyBearModulus
  | 4 | 5 | 10 | 48 | 60 => 1
  | 6 | 21 => 2
  | 13 | 15 => 4
  | 20 | 28 => 64
  | 11 | 35 => if byte then 1 else 0
  | 19 => if byte then 1 else 2
  | 25 => if byte then 171 else 65535
  | 31 => 4660
  | 32 => 22136
  | 33 | 53 => if byte then 43828 else 4660
  | 34 | 56 => if byte then 22136 else 65535
  | 36 => if byte then 0 else 1
  | 43 | 45 => if byte then 52 else 22016
  | 44 => if byte then 70196 else 22136
  | 49 => if byte then 20971520 else 12582912
  | 50 => if byte then 131243 else 0
  | 51 | 52 => if byte then 65707 else 0
  | 54 | 55 => if byte then 43776 else 0
  | 59 | 61 => if byte then 29 else 0
  | _ => 0

set_option maxRecDepth 4096 in
private theorem satisfies_store (byte : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (storeRow byte))
      (SubwordMemory.importedConstraints (Verification.subwordTable (fun _ => 0))) := by
  cases byte <;>
    simp [SubwordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, storeRow, Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (refine ⟨⟨201269, by decide⟩, ?_⟩
       norm_num [Verification.subwordRow, Verification.subwordDataRow, Verification.subwordStoreContribution])
    | (refine ⟨⟨65708, by decide⟩, ?_⟩
       norm_num [Verification.subwordRow, Verification.subwordDataRow, Verification.subwordStoreContribution])
    | (refine ⟨⟨153209, by decide⟩, ?_⟩
       norm_num [Verification.subwordRow, Verification.subwordDataRow, Verification.subwordStoreContribution])
    | (refine ⟨⟨0, by decide⟩, ?_⟩
       norm_num [Verification.subwordRow, Verification.subwordDataRow])

example : Word.mk ((storeRow true) 33).val ((storeRow true) 34).val = Word.mk 43828 22136 := by
  have result := SubwordMemory.Proofs.store_data (p := babyBearModulus)
    (source := ⟨171, 0⟩) (old := ⟨4660, 22136⟩) (by decide) true true false
    (satisfies_store true) rfl rfl rfl rfl rfl rfl ⟨rfl, rfl, rfl⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  exact result.2

example : Word.mk ((storeRow false) 33).val ((storeRow false) 34).val = Word.mk 4660 65535 := by
  have result := SubwordMemory.Proofs.store_data (p := babyBearModulus)
    (source := ⟨65535, 0⟩) (old := ⟨4660, 22136⟩) (by decide) false false true
    (satisfies_store false) rfl rfl rfl rfl rfl rfl ⟨rfl, rfl, rfl⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  exact result.2

-- The actual native state update agrees with SB/SH, including untouched bytes.
example : Reference.Sail.run
    (Reference.RiscV.Sail.writeMemory (size := 4) (BitVec.ofNat 32 4194304) (Word.mk 43828 22136).toBitVec)
    nativeState = Reference.Sail.run
    (Reference.RiscV.Sail.writeMemory (size := 1) (BitVec.ofNat 32 4194305) (BitVec.ofNat 8 171))
    nativeState := by
  have encoded := SubwordMemory.Proofs.store_byte_encoding (p := babyBearModulus)
    (source := ⟨171, 0⟩) (old := ⟨4660, 22136⟩) (by decide) true true false
    (satisfies_store true) rfl rfl rfl rfl rfl rfl ⟨rfl, rfl, rfl⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide)
  have output : Word.mk ((storeRow true) 33).val ((storeRow true) 34).val = Word.mk 43828 22136 := by decide
  rw [output] at encoded
  exact Reference.RiscV.Sail.write_subword_memory (before := nativeState)
    (BitVec.ofNat 32 4194304) (Word.mk 4660 22136).toBitVec (Word.mk 43828 22136).toBitVec
    true 1 (by decide) (by decide) (by decide) (BitVec.ofNat 8 171)
    (Reference.RiscV.Sail.read_word_memory nativeRead) encoded

example : Reference.Sail.run
    (Reference.RiscV.Sail.writeMemory (size := 4) (BitVec.ofNat 32 4194304) (Word.mk 4660 65535).toBitVec)
    nativeState = Reference.Sail.run
    (Reference.RiscV.Sail.writeMemory (size := 2) (BitVec.ofNat 32 4194306) (BitVec.ofNat 16 65535))
    nativeState := by
  have encoded := SubwordMemory.Proofs.store_byte_encoding (p := babyBearModulus)
    (source := ⟨65535, 0⟩) (old := ⟨4660, 22136⟩) (by decide) false false true
    (satisfies_store false) rfl rfl rfl rfl rfl rfl ⟨rfl, rfl, rfl⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide)
  have output : Word.mk ((storeRow false) 33).val ((storeRow false) 34).val = Word.mk 4660 65535 := by decide
  rw [output] at encoded
  exact Reference.RiscV.Sail.write_subword_memory (before := nativeState)
    (BitVec.ofNat 32 4194304) (Word.mk 4660 22136).toBitVec (Word.mk 4660 65535).toBitVec
    false 2 (by decide) (by decide) (by decide) (BitVec.ofNat 16 65535)
    (Reference.RiscV.Sail.read_word_memory nativeRead) encoded

-- Signed ROM loads exercise both key layouts against an independently fixed image.
private def romWord (byte : Bool) : BitVec 32 :=
  (if byte then Word.mk 65332 22136 else Word.mk 4660 32768).toBitVec

private def romRow (byte : Bool) : Nat → ZMod babyBearModulus
  | 4 | 5 | 40 | 41 | 46 | 60 | 12 => 1
  | 7 | 27 => 2
  | 13 | 15 | 21 | 39 => 4
  | 11 | 35 => if byte then 1 else 0
  | 19 => if byte then 5 else 6
  | 33 | 53 | 55 => if byte then 65535 else 32768
  | 34 | 54 | 56 | 58 => 65535
  | 36 => if byte then 0 else 1
  | 42 => 65472
  | 44 | 51 => if byte then 65536 else 0
  | 49 | 52 => if byte then 20971524 else 12582916
  | 50 => if byte then 196608 else 65536
  | 57 => if byte then 65535 else 32768
  | 59 | 61 => if byte then 45 else 44
  | _ => 0

set_option maxRecDepth 4096 in
private theorem satisfies_rom (byte : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (romRow byte))
      (SubwordMemory.importedConstraints (Verification.subwordTable (fun _ => romWord byte))) := by
  cases byte <;>
    simp [SubwordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, romRow, Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (refine ⟨⟨131073, by decide⟩, ?_⟩
       norm_num [Verification.subwordRow, Verification.subwordDataRow, Verification.subwordStoreContribution])
    | (refine ⟨⟨196609, by decide⟩, ?_⟩
       norm_num [Verification.subwordRow, Verification.subwordDataRow, Verification.subwordStoreContribution])
    | (refine ⟨⟨655368, by decide⟩, ?_⟩
       norm_num [romWord, Word.toBitVec, Word.value, limbBase, Verification.subwordRow,
         Verification.subwordDataRow, Verification.subwordLoadLimbs])
    | (refine ⟨⟨4849678, by decide⟩, ?_⟩
       norm_num [romWord, Word.toBitVec, Word.value, limbBase, Verification.subwordRow,
         Verification.subwordDataRow, Verification.subwordLoadLimbs])

example (byte : Bool) : (Word.mk ((romRow byte) 33).val ((romRow byte) 34).val).toBitVec =
    SailRV32.Functions.extend_value false
      ((romWord byte >>> (if byte then 8 else 16)).setWidth (8 * (if byte then 1 else 2))) := by
  have result := SubwordMemory.Proofs.rom_load_data (p := babyBearModulus)
    (cell := ⟨4, 0⟩) (by decide) byte true byte (!byte) (satisfies_rom byte)
    rfl rfl rfl rfl rfl rfl (by cases byte <;> rfl) ⟨rfl, rfl⟩
    ⟨by decide, by decide⟩ (by decide) (by cases byte <;> decide)
  cases byte <;> simpa only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false,
    if_true, Bool.not_true, Nat.reduceAdd, Nat.reduceMul] using result.2

end Tests.SubwordMemory

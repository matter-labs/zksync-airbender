import Airbender.Proofs.SubwordMemory
import Airbender.Proofs.BabyBear

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
private def row : Nat → ZMod babyBearModulus
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
private theorem satisfies_setup :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (SubwordMemory.importedConstraints (Verification.subwordTable (fun _ => 0))) := by
  apply satisfies_table
  intro i
  fin_cases i
  · refine ⟨⟨196609, by decide⟩, ?_⟩
    norm_num [fixtureRow, Verification.subwordRow, Verification.subwordDataRow,
      Verification.subwordLoadLimbs]
  · refine ⟨⟨528949, by decide⟩, ?_⟩
    norm_num [fixtureRow, Verification.subwordRow, Verification.subwordDataRow,
      Verification.subwordLoadLimbs]

example : (Word.mk (row 33).val (row 34).val).Bounded :=
  SubwordMemory.Proofs.ram_output_bounds (p := babyBearModulus) (by decide) true
    satisfies_setup rfl rfl rfl rfl

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

end Tests.SubwordMemory

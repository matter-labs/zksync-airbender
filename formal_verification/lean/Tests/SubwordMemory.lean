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
private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (SubwordMemory.importedConstraints fixture) := by
  simp [SubwordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, row, Lookup.Contains,
    fixture, Table.fromStatic, Table.toRaw]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩

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

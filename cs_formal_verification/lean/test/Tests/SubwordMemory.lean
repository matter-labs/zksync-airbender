module
public import Human.Circuits.SubwordMemory.Output
public import Human.Helpers.Core.BabyBearPrime
public import Slop.AddSub.Selectors
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.MulDiv.Values
public import Slop.SubwordMemory.Values
public import Slop.Trace.RowContext
public import Slop.Trace.CompositionCore
public import Slop.SubwordMemory.Stores
public import Slop.SubwordMemory.WitnessCheck
public import Slop.KernelRfl

@[expose] public section

namespace Tests.SubwordMemory
open Airbender Airbender.Arithmetic

-- Two independently fixed rows exercise the imported clearing and RAM-byte
-- queries. They are a boundary fixture, not a replacement setup table.
def fixtureRow (i : Fin 2) : Vector (ZMod babyBearModulus) 9 :=
  if i.val = 0 then #v[65536, 0, 0, 0, 0, 0, 0, 0, 30]
  else #v[135732, 18, 0, 0, 0, 0, 0, 0, 43]

def fixture : Table (ZMod babyBearModulus) (fields 9) := .fromStatic {
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

private theorem satisfies_table (setup : Table (ZMod babyBearModulus) (fields 9))
    (members : ∀ i : Fin 2, setup.Contains #[] (fixtureRow i)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (SubwordMemory.importedConstraints setup) :=
  SubwordMemory.holds_of_check
    (Verification.rowsChecked setup.toRaw [fixtureRow 0, fixtureRow 1] fun row mem => by
      obtain ⟨i, rfl⟩ : ∃ i, row = fixtureRow i := by
        rcases List.mem_cons.mp mem with rfl | mem
        · exact ⟨0, rfl⟩
        rcases List.mem_cons.mp mem with rfl | mem
        · exact ⟨1, rfl⟩
        exact absurd mem List.not_mem_nil
      simp only [Table.toRaw, Array.map_empty]
      exact members i)
    rfl (by kernel_rfl)

theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (SubwordMemory.importedConstraints fixture) :=
  satisfies_table fixture (fun i => ⟨i, rfl⟩)

-- The same complete LBU witness also satisfies the full reconstructed setup.
theorem satisfies_setup :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (SubwordMemory.importedConstraints (Verification.subwordTable (fun _ => 0))) :=
  SubwordMemory.holds_of_check (SubwordMemory.subwordChecked _) rfl (by kernel_rfl)

example : (Word.mk (row 33).val (row 34).val).Bounded :=
  SubwordMemory.Proofs.ram_output_bounds (p := babyBearModulus) (by decide) true
    satisfies_setup rfl rfl rfl rfl

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
def storeRow (byte : Bool) : Nat → ZMod babyBearModulus
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

theorem satisfies_store (byte : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (storeRow byte))
      (SubwordMemory.importedConstraints (Verification.subwordTable (fun _ => 0))) := by
  cases byte <;> exact SubwordMemory.holds_of_check (SubwordMemory.subwordChecked _) rfl (by kernel_rfl)

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

private theorem satisfies_rom (byte : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (romRow byte))
      (SubwordMemory.importedConstraints (Verification.subwordTable (fun _ => romWord byte))) := by
  cases byte <;> exact SubwordMemory.holds_of_check (SubwordMemory.subwordChecked _) rfl (by kernel_rfl)

end Tests.SubwordMemory

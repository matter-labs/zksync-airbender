import Airbender.Proofs.Tables.ImportedSubwordROMGeometry
import Airbender.Proofs.Tables.ImportedSubwordFixedRows
import Airbender.Review.Helpers.Tables.Subword

namespace Airbender.Verification
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem subwordImportedLimbs_eq_reference (byte : Bool) (key : Nat)
    (bound : key < if byte then 262144 else 131072) :
    subwordImportedLimbs byte key = subwordLoadLimbs byte key := by
  cases byte
  · have values := SubwordFixed.loadHalf_outputs key bound
    have small : key < loadHalfData.length := bound
    simp only [subwordImportedLimbs, Bool.false_eq_true, if_false,
      Nat.mod_eq_of_lt small]
    exact Prod.ext (congrArg (fun value => value.getD 0) values.1)
      (congrArg (fun value => value.getD 0) values.2)
  · have values := SubwordFixed.loadByte_outputs key bound
    have small : key < loadByteData.length := bound
    simp only [subwordImportedLimbs, reduceIte,
      Nat.mod_eq_of_lt small]
    exact Prod.ext (congrArg (fun value => value.getD 0) values.1)
      (congrArg (fun value => value.getD 0) values.2)

private def programKey (program : Nat → BitVec 32) (byte : Bool) (n : Nat) : Nat :=
  let group := if byte then 8 else 4
  let signed := n / (group / 2) % 2
  let highHalf := if byte then n / 2 % 2 else n % 2
  let highByte := if byte then n % 2 else 0
  let half := (program (n / group)).toNat / (if highHalf = 1 then 65536 else 1) % 65536
  half + 65536 * signed + 131072 * highByte

private def mathematicalROM (program : Nat → BitVec 32) (byte : Bool) (n : Nat) : Vector Nat 9 :=
  let outputs := subwordLoadLimbs byte (programKey program byte n)
  subwordDataRow (SubwordROMGeometry.key byte n) outputs.1 outputs.2 (subwordROMRegion byte).id

private theorem program_row (program : Nat → BitVec 32) (byte : Bool) (n : Nat)
    (bound : n < (subwordROMData byte).length) :
    subwordProgramROMRow program byte n = mathematicalROM program byte n := by
  have keyBound : programKey program byte n < if byte then 262144 else 131072 := by
    cases byte <;> simp only [programKey, Bool.false_eq_true, reduceIte] <;> omega
  have fields := SubwordROMGeometry.row byte n
    (subwordImportedLimbs byte (programKey program byte n)).1
    (subwordImportedLimbs byte (programKey program byte n)).2 bound
  have actual : subwordProgramROMRow program byte n =
      subwordDataRow (SubwordROMGeometry.key byte n)
        (subwordImportedLimbs byte (programKey program byte n)).1
        (subwordImportedLimbs byte (programKey program byte n)).2 (subwordROMRegion byte).id := by
    simpa only [subwordProgramROMRow, programKey, subwordDataRow] using fields
  exact actual.trans (congrArg (fun outputs : Nat × Nat =>
    subwordDataRow (SubwordROMGeometry.key byte n) outputs.1 outputs.2 (subwordROMRegion byte).id)
      (subwordImportedLimbs_eq_reference byte (programKey program byte n) keyBound))

private def referenceHalfROM (program : Nat → BitVec 32) (n : Nat) : Vector Nat 9 :=
  let half := (program (n / 4)).toNat / (if n % 2 = 1 then 65536 else 1) % 65536
  let data := subwordLoadLimbs false (half + 65536 * (n / 2 % 2))
  subwordDataRow (4 * (n / 4) + 4194304 * (n / 2 % 2) + 8388608 * (n % 2)) data.1 data.2 44

private def referenceByteROM (program : Nat → BitVec 32) (n : Nat) : Vector Nat 9 :=
  let half := (program (n / 8)).toNat / (if n / 2 % 2 = 1 then 65536 else 1) % 65536
  let data := subwordLoadLimbs true (half + 65536 * (n / 4 % 2) + 131072 * (n % 2))
  subwordDataRow
    (4 * (n / 8) + 4194304 * (n / 4 % 2) + 8388608 * (n / 2 % 2) + 16777216 * (n % 2))
    data.1 data.2 45

private theorem half_rom (program : Nat → BitVec 32) (n : Nat) (bound : n < 4194304) :
    subwordProgramROMRow program false n = referenceHalfROM program n := by
  apply (program_row program false n bound).trans
  simp only [mathematicalROM, programKey, SubwordROMGeometry.key, referenceHalfROM,
    Bool.false_eq_true, reduceIte, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero,
    show (subwordROMRegion false).id = 44 from rfl]

private theorem byte_rom (program : Nat → BitVec 32) (n : Nat) (bound : n < 8388608) :
    subwordProgramROMRow program true n = referenceByteROM program n := by
  apply (program_row program true n bound).trans
  simp only [mathematicalROM, programKey, SubwordROMGeometry.key, referenceByteROM,
    reduceIte, Nat.reduceDiv, show (subwordROMRegion true).id = 45 from rfl]

private def assembled (zero : Vector Nat 9)
    (place clear half byte halfROM byteROM : Nat → Vector Nat 9) (n : Nat) : Vector Nat 9 :=
  if n = 0 then zero
  else if n < 131073 then place (n - 1)
  else if n < 262145 then clear (n - 131073)
  else if n < 393217 then half (n - 262145)
  else if n < 655361 then byte (n - 393217)
  else if n < 4849665 then halfROM (n - 655361)
  else byteROM (n - 4849665)

private theorem assembled_congr
    (zero zero' : Vector Nat 9)
    (place clear half byte halfROM byteROM place' clear' half' byte' halfROM' byteROM' :
      Nat → Vector Nat 9)
    (hzero : zero = zero')
    (hplace : ∀ n, n < 131072 → place n = place' n)
    (hclear : ∀ n, n < 131072 → clear n = clear' n)
    (hhalf : ∀ n, n < 131072 → half n = half' n)
    (hbyte : ∀ n, n < 262144 → byte n = byte' n)
    (hhalfROM : ∀ n, n < 4194304 → halfROM n = halfROM' n)
    (hbyteROM : ∀ n, n < 8388608 → byteROM n = byteROM' n)
    (n : Nat) (bound : n < 13238273) :
    assembled zero place clear half byte halfROM byteROM n =
      assembled zero' place' clear' half' byte' halfROM' byteROM' n := by
  unfold assembled
  split_ifs with h0 h1 h2 h3 h4 h5
  · exact hzero
  · exact hplace (n - 1) (by omega)
  · exact hclear (n - 131073) (by omega)
  · exact hhalf (n - 262145) (by omega)
  · exact hbyte (n - 393217) (by omega)
  · exact hhalfROM (n - 655361) (by omega)
  · exact hbyteROM (n - 4849665) (by omega)

private def referencePlace (n : Nat) := subwordDataRow n (subwordStoreContribution false n) 0 29
private def referenceClear (n : Nat) := subwordDataRow n (subwordStoreContribution true n) 0 30
private def referenceHalf (n : Nat) :=
  subwordDataRow n (subwordLoadLimbs false n).1 (subwordLoadLimbs false n).2 42
private def referenceByte (n : Nat) :=
  subwordDataRow n (subwordLoadLimbs true n).1 (subwordLoadLimbs true n).2 43

private theorem place_row (n : Nat) (bound : n < 131072) :
    subwordFixedRow 0 n = referencePlace n := SubwordFixed.fixed_row 0 n bound
private theorem clear_row (n : Nat) (bound : n < 131072) :
    subwordFixedRow 1 n = referenceClear n := SubwordFixed.fixed_row 1 n bound
private theorem half_row (n : Nat) (bound : n < 131072) :
    subwordFixedRow 2 n = referenceHalf n := SubwordFixed.fixed_row 2 n bound
private theorem byte_row (n : Nat) (bound : n < 262144) :
    subwordFixedRow 3 n = referenceByte n := SubwordFixed.fixed_row 3 n bound

private theorem imported_assembly (program : Nat → BitVec 32) (index : Fin 13238273) :
    subwordNativeRow program index = assembled
      (subwordZeroData.columns.map (fun column => (column.get? 0).getD 0))
      (subwordFixedRow 0) (subwordFixedRow 1) (subwordFixedRow 2) (subwordFixedRow 3)
      (subwordProgramROMRow program false) (subwordProgramROMRow program true) index.val := by
  rfl

private theorem reference_assembly (program : Nat → BitVec 32) (index : Fin 13238273) :
    assembled (#v[0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector Nat 9)
      referencePlace referenceClear referenceHalf referenceByte
      (referenceHalfROM program) (referenceByteROM program) index.val =
        referenceSubwordRow program index := by
  rfl

private theorem assembled_fixed (zero : Vector Nat 9)
    (place clear half byte halfROM byteROM halfROM' byteROM' : Nat → Vector Nat 9)
    (n : Nat) (bound : n < 655361) :
    assembled zero place clear half byte halfROM byteROM n =
      assembled zero place clear half byte halfROM' byteROM' n := by
  unfold assembled
  split_ifs <;> rfl

private theorem assembled_half (zero : Vector Nat 9)
    (place clear half byte halfROM byteROM : Nat → Vector Nat 9)
    (n : Nat) (lower : 655361 ≤ n) (upper : n < 4849665) :
    assembled zero place clear half byte halfROM byteROM n = halfROM (n - 655361) := by
  unfold assembled
  simp only [if_neg (show n ≠ 0 by omega), if_neg (show ¬n < 131073 by omega),
    if_neg (show ¬n < 262145 by omega), if_neg (show ¬n < 393217 by omega),
    if_neg (show ¬n < 655361 by omega), if_pos upper]

private theorem assembled_byte (zero : Vector Nat 9)
    (place clear half byte halfROM byteROM : Nat → Vector Nat 9)
    (n : Nat) (lower : 4849665 ≤ n) :
    assembled zero place clear half byte halfROM byteROM n = byteROM (n - 4849665) := by
  unfold assembled
  simp only [if_neg (show n ≠ 0 by omega), if_neg (show ¬n < 131073 by omega),
    if_neg (show ¬n < 262145 by omega), if_neg (show ¬n < 393217 by omega),
    if_neg (show ¬n < 655361 by omega), if_neg (show ¬n < 4849665 by omega)]

theorem subword_fixed_independent (left right : Nat → BitVec 32) (index : Fin 13238273)
    (bound : index.val < 655361) : subwordNativeRow left index = subwordNativeRow right index := by
  exact (imported_assembly left index).trans
    ((assembled_fixed _ _ _ _ _ _ _ _ _ index.val bound).trans
      (imported_assembly right index).symm)

theorem subword_half_slice (program : Nat → BitVec 32) (index : Fin 13238273)
    (lower : 655361 ≤ index.val) (upper : index.val < 4849665) :
    subwordNativeRow program index = subwordProgramROMRow program false (index.val - 655361) := by
  exact (imported_assembly program index).trans
    (assembled_half _ _ _ _ _ _ _ index.val lower upper)

theorem subword_byte_slice (program : Nat → BitVec 32) (index : Fin 13238273)
    (lower : 4849665 ≤ index.val) :
    subwordNativeRow program index = subwordProgramROMRow program true (index.val - 4849665) := by
  exact (imported_assembly program index).trans
    (assembled_byte _ _ _ _ _ _ _ index.val lower)

/-- Reuse the existing arbitrary-program proofs through a characterization
    proved from every imported fixed row. No equivalence is assumed. -/
theorem subwordNativeRow_eq_reference (program : Nat → BitVec 32) (index : Fin 13238273) :
    subwordNativeRow program index = referenceSubwordRow program index := by
  exact (imported_assembly program index).trans
    ((assembled_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ SubwordFixed.zero_row
      place_row clear_row half_row byte_row (half_rom program) (byte_rom program)
      index.val index.isLt).trans (reference_assembly program index))

end Airbender.Verification

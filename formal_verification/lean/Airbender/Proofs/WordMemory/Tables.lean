import Airbender.Proofs.WordMemory.ArtifactChecks
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Arithmetic.Lemmas

namespace Airbender.WordMemory.Proofs
open Verification

variable {p : Nat} [Fact p.Prime] {rom : WordROM} {w : Nat → ZMod p}

theorem separator_query
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    ∃ i : Fin 65536, #v[w 20, w 22, w 23] = (romSeparatorRow i).map Nat.cast := by
  have query := lookup_of_holds h ⟨10, by rw [lookup_count]; decide⟩
  simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, fixed3,
    Table.toRaw, romSeparatorTable, Table.fromStatic, StaticTable.toTable,
    Expression.eval, environment, ProvableType.fromElements] using query

theorem rom_query
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    ∃ i : Fin 1048576, #v[w 19 + 65536 * w 23, w 26, w 27] =
      (rom.row i).map Nat.cast := by
  have query := lookup_of_holds h ⟨11, by rw [lookup_count]; decide⟩
  simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, fixed3,
    Table.toRaw, romWordTable, Table.fromStatic, StaticTable.toTable,
    Expression.eval, environment, ProvableType.fromElements] using query

theorem address_bounds
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    (w 19).val < 65536 ∧ (w 20).val < 65536 := by
  have lo := range16_bound (lookup_of_holds h ⟨0, by rw [lookup_count]; decide⟩)
  have hi := range16_bound (lookup_of_holds h ⟨1, by rw [lookup_count]; decide⟩)
  exact ⟨lo, hi⟩

theorem separator_values (hp : 65536 < p)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    w 22 = (if (w 20).val < 64 then 0 else 1) ∧
    w 23 = ((w 20).val % 64 : Nat) := by
  obtain ⟨i, row⟩ := separator_query h
  have high := congrArg (fun q => q[0]) row
  have ram := congrArg (fun q => q[1]) row
  have chunk := congrArg (fun q => q[2]) row
  simp [romSeparatorRow] at high ram chunk
  have index : (w 20).val = i.val := by
    rw [high, ZMod.val_natCast_of_lt (by have := i.isLt; omega)]
  simp only [index]
  exact ⟨by simpa only [Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using ram, chunk⟩

theorem rom_values (hp : 4194304 < p)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    (w 19).val % 4 = 0 ∧
    w 26 = ((rom.word (((w 19).val + 65536 * ((w 20).val % 64)) / 4)).toNat % 65536 : Nat) ∧
    w 27 = ((rom.word (((w 19).val + 65536 * ((w 20).val % 64)) / 4)).toNat / 65536 : Nat) := by
  have bounds := address_bounds h
  have separator := (separator_values (by omega) h).2
  obtain ⟨i, row⟩ := rom_query h
  have key := congrArg (fun q => q[0]) row
  have lo := congrArg (fun q => q[1]) row
  have hi := congrArg (fun q => q[2]) row
  simp [WordROM.row] at key lo hi
  have natural : (w 19).val + 65536 * ((w 20).val % 64) = 4 * i.val := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by have := Nat.mod_lt (w 20).val (by decide : 0 < 64); omega)
      (by have := i.isLt; omega)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      ZMod.natCast_zmod_val, ← separator] using key
  have index : ((w 19).val + 65536 * ((w 20).val % 64)) / 4 = i.val := by omega
  refine ⟨?_, ?_, ?_⟩
  · omega
  · simpa only [index] using lo
  · simpa only [index] using hi

end Airbender.WordMemory.Proofs

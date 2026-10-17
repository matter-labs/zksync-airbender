import Airbender.Review.Circuits.WordMemory.Theorems

namespace Tests.WordMemory
open Airbender Verification

private def rom : WordROM := ⟨[], by decide⟩

/-- Full native row with PC zero, time four and prior port timestamps zero. -/
private def row (store inROM discard : Bool) (i : Nat) : ZMod mersenne31Modulus :=
  let addressHi := if inROM then 0 else 64
  let rd := if store || discard then 0 else 3
  let candidateLo := if store then 0 else if inROM then 4211 else 123
  let candidateHi := if !store && inROM then 49152 else 0
  let writeLo := if store then 123 else if discard then 0 else candidateLo
  let writeHi := if discard then 0 else candidateHi
  if i = 2 then 4
  else if i = 4 ∨ i = 5 ∨ i = 49 ∨ i = 52 ∨ i = 55 then 1
  else if i = 6 then if store then 2 else 0
  else if i = 7 then rd
  else if i = 8 then if rd = 0 then 1 else 0
  else if i = 11 then 2
  else if i = 12 then if store then 1 else 0
  else if i = 13 then 4
  else if i = 15 then 8
  else if i = 17 ∨ i = 19 then 16
  else if i = 18 ∨ i = 20 then addressHi
  else if i = 22 then if inROM then 0 else 1
  else if i = 24 then if !store && inROM then 1 else 0
  else if i = 25 then if !store && !inROM then 1 else 0
  else if i = 26 then 4211
  else if i = 27 then 49152
  else if i = 28 then if store then 2 else 16
  else if i = 29 then if store then 0 else addressHi
  else if i = 30 then 123
  else if i = 32 then if store then 0 else 1
  else if i = 33 then if store then 16 else rd
  else if i = 34 then if store then addressHi else 0
  else if i = 37 then writeLo
  else if i = 38 then writeHi
  else if i = 39 then candidateLo
  else if i = 40 then candidateHi
  else if i = 41 then if discard then 0 else candidateLo
  else if i = 42 then if discard then 0 else candidateHi
  else if i = 43 then 1227138194
  else if i = 45 then 2147450879
  else 0

private theorem satisfies (store inROM discard : Bool) (legal : (store && inROM) = false) :
    FlatOperation.ConstraintsHoldFlat (environment (row store inROM discard))
      (Airbender.WordMemory.importedConstraints rom) := by
  cases store <;> cases inROM <;> cases discard <;> simp_all only [Bool.false_and,
    Bool.true_and, Bool.true_eq_false]
  all_goals
    simp [Airbender.WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, environment, row]
    repeat' apply And.intro
    all_goals first | (apply range16_contains; decide) |
      (apply timestamp19_contains; decide) | try decide
    all_goals
      simp only [Lookup.Contains, fixed3, Table.toRaw, romSeparatorTable,
        romWordTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
        Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, row]
      solve
      | refine ⟨⟨0, by decide⟩, ?_⟩
        norm_num [romSeparatorRow, WordROM.row, WordROM.word, rom]
      | refine ⟨⟨64, by decide⟩, ?_⟩
        norm_num [romSeparatorRow, WordROM.row, WordROM.word, rom]
      | refine ⟨⟨4, by decide⟩, ?_⟩
        norm_num [romSeparatorRow, WordROM.row, WordROM.word, rom]

theorem ram_load : Airbender.WordMemory.NativeTransfers rom (row false false false) :=
  Airbender.WordMemory.native_transfers rom _ (satisfies false false false rfl)

theorem ram_store : Airbender.WordMemory.NativeTransfers rom (row true false false) :=
  Airbender.WordMemory.native_transfers rom _ (satisfies true false false rfl)

theorem rom_load : Airbender.WordMemory.NativeTransfers rom (row false true false) :=
  Airbender.WordMemory.native_transfers rom _ (satisfies false true false rfl)

theorem discarded_rom_load :
    FlatOperation.ConstraintsHoldFlat (environment (row false true true))
      (Airbender.WordMemory.importedConstraints rom) ∧
    row false true true 37 = 0 ∧ row false true true 38 = 0 :=
  ⟨satisfies false true true rfl, rfl, rfl⟩

theorem rom_store_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (row true true false))
      (Airbender.WordMemory.importedConstraints rom) := by
  intro h
  have store := (Airbender.WordMemory.native_transfers rom _ h).store (by decide)
  have impossible := store.1
  revert impossible
  decide

theorem changed_rom_read_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 26 then 4212 else row false true false i))
      (Airbender.WordMemory.importedConstraints rom) := by
  intro h
  have value := (Airbender.WordMemory.Proofs.rom_values (by decide) h).2.1
  revert value
  decide

theorem unaligned_address_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 19 then 17 else row false false false i))
      (Airbender.WordMemory.importedConstraints rom) := by
  intro h
  have aligned := (Airbender.WordMemory.native_transfers rom _ h).addressAlignment
  revert aligned
  decide

theorem native_rom_padding : rom.word 0 = BitVec.ofNat 32 3221229683 ∧
    rom.word 1048575 = BitVec.ofNat 32 3221229683 := ⟨rfl, rfl⟩

end Tests.WordMemory

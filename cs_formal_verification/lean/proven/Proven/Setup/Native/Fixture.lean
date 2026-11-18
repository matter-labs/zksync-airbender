module
public import Human.Compiler.NativeSetups.Fixture
public import Proven.Compiler.ExecutableDecoder
public import Proven.Trace.Machine.Program
public import Proven.Setup.Imported
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/- The setup fixture program in the public setup: its ROM words, its empty decoder slots, and the public generic rows
   of a CPU circuit and the imported rows of a setup, from the column formulas of the setup. -/

namespace Airbender.Compiler.NativeSetups.Proofs
open Airbender Trace NativeArithmetic NativePublicSetup Metadata Import.Setup

/-- The fixture ROM holds no byte at an address from 16. -/
private theorem rom_high (address : BitVec 32) (high : 16 ≤ address.toNat) : fixtureInitial.rom address = 0 := by
  obtain ⟨key, equal⟩ : ∃ key, address.toNat / 4 = key + 4 := ⟨address.toNat / 4 - 4, by omega⟩
  simp only [fixtureInitial, equal, fixtureWords]
  simp

/-- The fixture ROM holds the fixture words at every aligned word address. -/
theorem words_fixture : ROM.wordsRV fixtureInitial = fixtureWords := by
  funext index
  by_cases small : index < 4
  · interval_cases index <;> decide +kernel
  have zero : fixtureWords index = 0 := by
    obtain ⟨key, rfl⟩ : ∃ key, index = key + 4 := ⟨index - 4, by omega⟩
    rfl
  rw [zero]
  unfold ROM.wordsRV
  split
  · rename_i fits
    have address (k : Nat) (inside : k < 4) :
        ((BitVec.ofNat 32 (4 * index) + BitVec.ofNat 32 k).toNat) = 4 * index + k := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [RV.RAM_END] at fits
      omega
    have b0 := rom_high (BitVec.ofNat 32 (4 * index) + BitVec.ofNat 32 0) (by rw [address 0 (by omega)]; omega)
    have b1 := rom_high (BitVec.ofNat 32 (4 * index) + BitVec.ofNat 32 1) (by rw [address 1 (by omega)]; omega)
    have b2 := rom_high (BitVec.ofNat 32 (4 * index) + BitVec.ofNat 32 2) (by rw [address 2 (by omega)]; omega)
    have b3 := rom_high (BitVec.ofNat 32 (4 * index) + BitVec.ofNat 32 3) (by rw [address 3 (by omega)]; omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1 b2 b3
    simp only [RV.read, BitVec.add_assoc] at *
    simp [b0, b1, b2, b3]
  · rfl

/-- Every entry of a fixture program sits below byte address 16. -/
theorem program_low (config : RVMachineConfig) : ∀ entry ∈ fixtureProgram config, entry.pc.toNat < 16 := by
  cases config <;> decide +kernel

/-- Decoder slots from 4 hold no entry of a fixture program. -/
theorem slot_empty (config : RVMachineConfig) {slot : Nat} (late : 4 ≤ slot) :
    rvMachineProgramSlot (fixtureProgram config) slot = none := by
  change (rvMachineProgramIndex (fixtureProgram config))[4 * slot]? = none
  rw [Trace.Machine.Proofs.machine_program_index_lookup, List.find?_eq_none]
  intro entry member
  have := program_low config entry member
  simp only [beq_iff_eq]
  omega

/-- A decoder slot without an entry holds the row of the empty slot. -/
theorem decoderRowNat_empty (family : RVMachineDecoderFamily) {slot : Nat → Option RVMachineProgramEntry}
    {index : Nat} (empty : slot index = none) :
    decoderRowNatWith family slot index = decoderRowNatWith family (fun _ => none) 0 := by
  simp only [decoderRowNatWith, empty]

/-- The stored form of the field element `-1` is `-1`. -/
theorem sentinel_cast : ((babyBearModulus - 1 : Nat) : F) = -1 := by
  decide +kernel

/-- The public generic rows of CPU circuit `family` for a fixture program are the values of the column formulas
    `formulas`: on the fixed region, on the first four decoder slots (the slots of the fixture words), on the later
    decoder slots and on the padding rows. -/
theorem genericRow_fixture (family : RVMachineDecoderFamily) (config : RVMachineConfig) (formulas : List (Nat → Nat))
    (fixed : ∀ n < offset family,
      fixedRow family fixtureWords n = (formulas.map (· n)).map fun value : Nat => (value : F))
    (early : ∀ slot < 4, decoderRowNatWith family (rvMachineProgramSlot (fixtureProgram config)) slot =
      formulas.map (· (offset family + slot)))
    (decoder : ∀ n, offset family + 4 ≤ n → n < offset family + decoderCapacity →
      formulas.map (· n) = decoderRowNatWith family (fun _ => none) 0)
    (padding : ∀ n, offset family + decoderCapacity ≤ n →
      formulas.map (· n) = List.replicate (width family) (if tagged family then 0 else babyBearModulus - 1))
    (n : Nat) :
    genericRow family fixtureInitial (fixtureProgram config) n =
      (formulas.map (· n)).map fun value : Nat => (value : F) := by
  simp only [genericRow, offset_binding, width_binding, words_fixture]
  by_cases inFixed : n < offset family
  · rw [ite_eq_left inFixed]
    exact fixed n inFixed
  rw [ite_eq_right inFixed]
  by_cases inDecoder : n - offset family < decoderCapacity
  · rw [ite_eq_left inDecoder, ← decoderRowNat_binding]
    congr 1
    by_cases first : n - offset family < 4
    · rw [early _ first, Nat.add_sub_cancel' (by omega)]
    · rw [decoderRowNat_empty family (slot_empty config (by omega)), decoder n (by omega) (by omega)]
  · rw [ite_eq_right inDecoder, padding n (by omega), List.map_replicate]
    cases tagged family <;> simp [sentinel_cast]

/-- The imported generic rows of row `n` of a setup are the values of its column formulas `formulas` at `n`. -/
theorem importedRows_formulas {data : SetupData} (formulas : List (Nat → Nat)) {n : Nat}
    (size : data.columns.size = formulas.length)
    (column : ∀ k (inside : k < formulas.length), decode (data.columns.getD k []) n = (formulas[k] n : Int)) :
    importedRows data 0 n = (formulas.map (· n)).map fun value : Nat => (value : F) := by
  unfold importedRows
  simp only [Fin.val_zero, ↓reduceIte, List.map_map]
  apply List.ext_getElem
  · simp [size]
  · intro k inside _
    have inside : k < formulas.length := by simpa [size] using inside
    have equal : decode data.columns[k] n = (formulas[k] n : Int) := by
      rw [← column k inside]
      simp [Array.getD, show k < data.columns.size by omega]
    simp [equal]

/-- A fixed row of natural numbers whose fields, as integers, are the values of the column formulas. -/
theorem fixed_formulas {width : Nat} (row : Vector Nat width) (formulas : List (Nat → Nat)) (n : Nat)
    (length : formulas.length = width)
    (each : ∀ k (inside : k < width), (row[k] : Int) = ((formulas[k]'(by omega)) n : Int)) :
    row.toList.map (fun value : Nat => (value : F)) = (formulas.map (· n)).map fun value : Nat => (value : F) := by
  congr 1
  apply List.ext_getElem
  · simp [length]
  · intro k inside _
    have inside : k < width := by simpa using inside
    simpa using each k inside

end Airbender.Compiler.NativeSetups.Proofs

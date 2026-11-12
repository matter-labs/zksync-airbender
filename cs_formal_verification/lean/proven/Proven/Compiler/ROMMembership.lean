module
public import Proven.Compiler.FixedMembership
public import Proven.Trace.InitialImage

@[expose] public section
namespace Airbender.Compiler.NativeFixedMembership
open Airbender Trace Arithmetic NativeArithmetic NativePublicSetup NativePublicSetup.Proofs
set_option warningAsError true

private theorem zip_map_member {α β : Type} (values : List α) (map : α → β) (value : α)
    (member : value ∈ values) : (value, map value) ∈ values.zip (values.map map) := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | rest
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih rest)

/-- Each tracked public ROM cell occurs with its actual public image word. -/
theorem rom_row_member (initial : RV.State) (cells : List Cell) (address : BitVec 32)
    (member : Cell.ram address ∈ cells) (rom : address.toNat < RV.ROM_END) :
    ROM.row (p := babyBearModulus) address (Word.ofBitVec (RV.read initial.rom address 4)) ∈
      ROM.rows cells (romImageRV initial cells) := by
  apply List.mem_cons_of_mem
  apply List.mem_filterMap.mpr
  refine ⟨(Cell.ram address, (Cell.ram address).initialToken (RV.read initial.rom address 4)), ?_, ?_⟩
  · exact zip_map_member cells (fun cell => cell.initialToken (match cell with
        | .register _ => 0 | .ram location => RV.read initial.rom location 4)) (Cell.ram address) member
  · simp only [rom, ite_true, Trace.Proofs.initial_token_word]

/-- Every native word-ROM row occurs in the public tracked ROM table. -/
theorem word_row_contains (initial : RV.State) (cells : List Cell) (covers : CoversROM cells)
    (index : Fin 1048577) (provided : Array (Vector F 9)) :
    (ROM.table (p := babyBearModulus) cells (romImageRV initial cells)).Contains provided
      ((NativeFixedRows.wordMemory (ROM.wordsRV initial) index).map (fun (n : Nat) => (n : F))) := by
  apply (ROM.table (p := babyBearModulus) cells (romImageRV initial cells)).implied_by_completeness provided
  change _ ∈ ROM.rows cells (romImageRV initial cells)
  by_cases zero : index.val = 0
  · simp [NativeFixedRows.wordMemory, zero, ROM.rows]
  · let key : Fin 1048576 := ⟨index.val - 1, by have bound := index.isLt; omega⟩
    let address : BitVec 32 := BitVec.ofNat 32 (4 * key.val)
    have small : 4 * key.val < 4194304 := by have bound := key.isLt; omega
    have addressValue : address.toNat = 4 * key.val := by
      dsimp [address]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      omega
    have inside : address.toNat < RV.ROM_END := by rw [addressValue]; exact small
    have fetched : ROM.wordsRV initial key.val = RV.read initial.rom address 4 := by
      unfold ROM.wordsRV
      rw [ite_eq_left (by have bound := key.isLt; change 4 * key.val + 4 ≤ 4294967296; omega)]
    have native : (NativeFixedRows.wordMemory (ROM.wordsRV initial) index).map (fun (n : Nat) => (n : F)) =
        ROM.row address (Word.ofBitVec (RV.read initial.rom address 4)) := by
      rw [NativeFixedRows.wordMemory, ite_eq_right zero]
      simp only [ROM.row, addressValue, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
      rw [fetched]
      simp [key]
    rw [native]
    exact rom_row_member initial cells address (covers key) inside

end Airbender.Compiler.NativeFixedMembership
namespace Airbender.Compiler.NativeFixedMembership
open Airbender Trace Arithmetic NativeArithmetic NativePublicSetup NativePublicSetup.Proofs NativePublicSetup.Metadata
set_option warningAsError true

/-- Native word lookup matching supplies the public tracked ROM table. -/
theorem word_contains {initial : RV.State} {program : List RVMachineProgramEntry}
    {actual : ProgramLookupRows} (bound : Bound initial program actual) (cells : List Cell)
    (covers : CoversROM cells) (value : Vector F 9)
    (member : Contains initial program (.pooled .wordMemory) 0 value.toList)
    (unused : value[7] = 0) (provided : Array (Vector F 9)) :
    (ROM.table (p := babyBearModulus) cells (romImageRV initial cells)).Contains provided value := by
  have zero : (value.toList[maskColumn (.pooled .wordMemory)]?).getD 0 = 0 := by
    simpa [maskColumn, hasFunct3] using unused
  rcases fixed_or_padding bound (.pooled .wordMemory) rfl value.toList member zero with fixed | padding
  · obtain ⟨index, _, same⟩ := fixed
    have equal : value = (NativeFixedRows.wordMemory (ROM.wordsRV initial) (Fin.ofNat 1048577 index)).map
        (fun (n : Nat) => (n : F)) := by
      apply Vector.toList_inj.mp
      simpa only [NativePublicSetup.fixedRow, Vector.toList_map] using same
    rw [equal]
    exact word_row_contains initial cells covers _ provided
  · apply (ROM.table (p := babyBearModulus) cells (romImageRV initial cells)).implied_by_completeness provided
    change value ∈ ROM.rows cells (romImageRV initial cells)
    have equal : value = Vector.replicate 9 0 := by
      apply Vector.toList_inj.mp
      simpa [width, hasFunct3] using padding
    rw [equal]
    exact List.mem_cons_self

end Airbender.Compiler.NativeFixedMembership

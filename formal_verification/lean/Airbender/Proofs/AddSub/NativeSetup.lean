import Airbender.Review.Circuits.AddSub.Tables.NativeSetupData
import Airbender.Proofs.Trace.SparseDecoderSetup
import Airbender.Proofs.Trace.DecoderSetup
import Airbender.Proofs.Mersenne31

namespace Airbender.AddSub.Proofs
open Verification Trace Setup NativeSetup

/-- Each literal public word is read through original Sail byte memory. -/
theorem native_fixture_words (i : Fin 7) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before = .ok words[i.val] before := by
  fin_cases i <;>
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, words, Std.ExtHashMap.getElem_insert]

set_option maxRecDepth 32768 in
/-- The table's supported entries are constructed from actual public bytes and
    the original Sail decoder; the intervening unsupported word remains a hole. -/
theorem native_fixture_image : sparseDecoderSetupImageWith decoderFields before 7 20 = some setup := by
  have slots : ([0,4,8,12,16,20,24] : List (BitVec 32)).mapM (programSlotWith decoderFields before) =
      some setup.slots := by
    simp only [List.mapM_cons, List.mapM_nil, programSlotWith,
      show (Cell.ram 0).read before = .ok (0x001080b3 : BitVec 32) before from native_fixture_words ⟨0, by decide⟩,
      show (Cell.ram 4).read before = .ok (0xfff08113 : BitVec 32) before from native_fixture_words ⟨1, by decide⟩,
      show (Cell.ram 8).read before = .ok (0x40208033 : BitVec 32) before from native_fixture_words ⟨2, by decide⟩,
      show (Cell.ram 12).read before = .ok (0x000071b7 : BitVec 32) before from native_fixture_words ⟨3, by decide⟩,
      show (Cell.ram 16).read before = .ok (0x00005217 : BitVec 32) before from native_fixture_words ⟨4, by decide⟩,
      show (Cell.ram 20).read before = .ok (0xc0001073 : BitVec 32) before from native_fixture_words ⟨5, by decide⟩,
      show (Cell.ram 24).read before = .ok (0x001080b3 : BitVec 32) before from native_fixture_words ⟨6, by decide⟩,
      bind, Option.bind]
    cbv
  change (([0,4,8,12,16,20,24] : List (BitVec 32)).mapM (programSlotWith decoderFields before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048569)) = some setup
  rw [slots]
  rfl

/-- Every exported unsupported tail cell is checked symbolically, without
    reducing a million rows. The seven original slots are handled separately. -/
theorem native_exported_tail (i : Fin 1048576) (tail : 7 ≤ i.val) :
    arithmeticDecoder.rowNat i = Vector.replicate 10 2147483646 := by
  have column (values : Array Nat) (size : values.size = 7) :
      (getFromBlocks [.dense values, .affine 1048569 2147483646 (Int.ofNat 0)] i.val).getD 0 = 2147483646 := by
    simp only [getFromBlocks, Block.length, size]
    rw [if_neg (by omega : ¬i.val < 7), if_pos (by have := i.isLt; omega)]
    simp [Block.get?, Block.length, show i.val - 7 < 1048569 by have := i.isLt; omega]
  have mixed (first step : Nat) (values : Array Nat) (size : values.size = 2) :
      (getFromBlocks [.affine 5 first (Int.ofNat step), .dense values,
        .affine 1048569 2147483646 (Int.ofNat 0)] i.val).getD 0 = 2147483646 := by
    simp only [getFromBlocks, Block.length, size]
    rw [if_neg (by omega : ¬i.val < 5), if_neg (by omega : ¬i.val - 5 < 2),
      if_pos (by have := i.isLt; omega)]
    simp [Block.get?, Block.length, show i.val - 5 - 2 < 1048569 by have := i.isLt; omega]
  ext k bound
  interval_cases k <;> simp only [TableData.rowNat, arithmeticDecoder, Vector.getElem_map,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    Vector.getElem_replicate, Column.get?]
  all_goals first | exact column _ rfl | exact mixed _ _ _ rfl

/-- Exact row equality is proved from the actual export and constructed public
    setup; it is never supplied as a premise to decoder soundness. -/
theorem native_exported_rows (i : Fin 1048576) :
    arithmeticDecoder.row (p := mersenne31Modulus) i = setup.row i := by
  rcases i with ⟨n, bound⟩
  by_cases early : n < 7
  · interval_cases n <;> decide +kernel +revert
  · have tail := native_exported_tail ⟨n,bound⟩ (by simpa only [Fin.val_mk] using Nat.le_of_not_gt early)
    rw [TableData.row, tail]
    have absent : setup.slots[n]? = none := List.getElem?_eq_none (by simpa [setup] using Nat.le_of_not_gt early)
    simp [SparseDecoderSetup.row, absent]
    decide

/-- Actual native regional membership supplies public original Sail evidence.
    The accepted native row equations themselves exclude both the hole and tail. -/
theorem native_exported_source {row : Row mersenne31Modulus}
    (constraints : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (row.constraints ()))
    (member : ∃ i : Fin 1048576, row.decoderQuery = arithmeticDecoder.row i) :
    ∃ entry ∈ setup.program, entry.Source before ∧ row.decoderQuery = entry.query := by
  have logical : setup.table.Contains #[] row.decoderQuery := by
    obtain ⟨i, same⟩ := member
    exact ⟨i, same.trans (native_exported_rows i)⟩
  have active : row.decoderQuery ≠ Vector.replicate 10 (-1) := by
    cases row with
    | mk family w => cases family; exact Trace.Proofs.padding_excluded (by decide) constraints
  obtain ⟨entry, present, same⟩ := Trace.Proofs.sparse_member logical active
  exact ⟨entry, present, (Airbender.Trace.Proofs.sparse_setup_sources native_fixture_image present).1, same⟩

end Airbender.AddSub.Proofs

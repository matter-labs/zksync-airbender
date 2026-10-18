import Airbender.Review.Circuits.WordMemory.Tables.NativeSparseData
import Airbender.Proofs.Trace.Families.WordMemory.SparseDecoder
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory.Proofs
open Verification Trace Setup NativeSparse

/-- Each literal public word is read through original Sail byte memory. -/
theorem sparse_fixture_words (i : Fin 4) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before = .ok words[i.val] before := by
  fin_cases i <;>
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, words, Std.ExtHashMap.getElem_insert]

set_option maxRecDepth 32768 in
/-- The table's supported entries are constructed from actual public bytes and
    the original Sail decoder; the intervening unsupported word remains a hole. -/
theorem sparse_fixture_image : sparseDecoderSetupImage before 4 20 = some setup := by
  have slots : ([0,4,8,12] : List (BitVec 32)).mapM (programSlotWith decoderFields before) =
      some setup.slots := by
    simp only [List.mapM_cons, List.mapM_nil, programSlotWith,
      show (Cell.ram 0).read before = .ok (0x0100a183 : BitVec 32) before from sparse_fixture_words ⟨0, by decide⟩,
      show (Cell.ram 4).read before = .ok (0xc0001073 : BitVec 32) before from sparse_fixture_words ⟨1, by decide⟩,
      show (Cell.ram 8).read before = .ok (0x0030a823 : BitVec 32) before from sparse_fixture_words ⟨2, by decide⟩,
      show (Cell.ram 12).read before = .ok (0x0100a003 : BitVec 32) before from sparse_fixture_words ⟨3, by decide⟩,
      bind, Option.bind]
    cbv
  change (([0,4,8,12] : List (BitVec 32)).mapM (programSlotWith decoderFields before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048572)) = some setup
  rw [slots]
  rfl

/-- Every exported unsupported tail cell is checked symbolically, without
    reducing a million rows. The four original slots are handled separately. -/
theorem sparse_exported_tail (i : Fin 1048576) (tail : 4 ≤ i.val) :
    holesDecoder.rowNat i = Vector.replicate 10 2147483646 := by
  have column (values : Array Nat) (size : values.size = 4) :
      (getFromBlocks [.dense values, .affine 1048572 2147483646 (Int.ofNat 0)] i.val).getD 0 = 2147483646 := by
    simp only [getFromBlocks, Block.length, size]
    rw [if_neg (by omega : ¬i.val < 4), if_pos (by have := i.isLt; omega)]
    simp [Block.get?, Block.length, show i.val - 4 < 1048572 by have := i.isLt; omega]
  ext k bound
  interval_cases k <;> simp only [TableData.rowNat, holesDecoder, Vector.getElem_map,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    Vector.getElem_replicate, Column.get?]
  all_goals exact column _ rfl

/-- Exact row equality is proved from the actual export and constructed public
    setup; it is never supplied as a premise to decoder soundness. -/
theorem sparse_exported_rows (i : Fin 1048576) :
    holesDecoder.row (p := mersenne31Modulus) i = setup.row i := by
  rcases i with ⟨n, bound⟩
  by_cases early : n < 4
  · interval_cases n <;> decide +kernel +revert
  · have tail := sparse_exported_tail ⟨n,bound⟩ (by simpa only [Fin.val_mk] using Nat.le_of_not_gt early)
    rw [TableData.row, tail]
    have absent : setup.slots[n]? = none := List.getElem?_eq_none (by simpa [setup] using Nat.le_of_not_gt early)
    simp [SparseDecoderSetup.row, absent]
    decide

/-- Actual native regional membership supplies public original Sail evidence.
    The accepted native row equations themselves exclude both the hole and tail. -/
theorem sparse_exported_source {rom : WordROM} {row : Row mersenne31Modulus WordMemoryFamily}
    (constraints : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (row.constraints rom))
    (member : ∃ i : Fin 1048576, row.decoderQuery = holesDecoder.row i) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query := by
  have logical : setup.table.Contains #[] row.decoderQuery := by
    obtain ⟨i, same⟩ := member
    exact ⟨i, same.trans (sparse_exported_rows i)⟩
  obtain ⟨entry, present, same⟩ := sparse_decoder_member (by decide) constraints logical
  exact ⟨entry, present, (Airbender.Trace.Proofs.sparse_setup_sources sparse_fixture_image present).1, same⟩

end Airbender.WordMemory.Proofs

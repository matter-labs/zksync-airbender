import Airbender.Review.Circuits.JumpBranchSlt.Tables.NativeSetupData
import Airbender.Proofs.JumpBranchSlt.Decoder

namespace Airbender.JumpBranchSlt.Proofs
open Verification Trace Setup NativeSetup

theorem native_fixture_words (i : Fin 3) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before =
      .ok words[i.val] before := by
  fin_cases i <;>
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, words, Std.ExtHashMap.getElem_insert]

set_option maxRecDepth 32768 in
theorem native_fixture_image : JumpBranchSlt.sparseDecoderSetupImage before 3 20 = some setup := by
  have slots : ([0,4,8] : List (BitVec 32)).mapM
      (programSlotWith JumpBranchSlt.decoderFields before) = some setup.slots := by
    simp only [List.mapM_cons, List.mapM_nil, programSlotWith,
      show (Cell.ram 0).read before = .ok (0xffdff0ef : BitVec 32) before from native_fixture_words ⟨0, by decide⟩,
      show (Cell.ram 4).read before = .ok (0xc0001073 : BitVec 32) before from native_fixture_words ⟨1, by decide⟩,
      show (Cell.ram 8).read before = .ok (0xfff0b013 : BitVec 32) before from native_fixture_words ⟨2, by decide⟩,
      bind, Option.bind]
    cbv
  change (([0,4,8] : List (BitVec 32)).mapM (programSlotWith JumpBranchSlt.decoderFields before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048573)) = some setup
  rw [slots]
  rfl

/-- Every exported unsupported tail cell is checked symbolically, without
    reducing a million rows. The three original slots are handled separately. -/
theorem native_exported_tail (i : Fin 1048576) (tail : 3 ≤ i.val) :
    controlDecoder.rowNat i = Vector.replicate 10 2147483646 := by
  have column (values : Array Nat) (size : values.size = 3) :
      (getFromBlocks [.dense values, .affine 1048573 2147483646 (Int.ofNat 0)] i.val).getD 0 = 2147483646 := by
    simp only [getFromBlocks, Block.length, size]
    rw [if_neg (by omega : ¬i.val < 3), if_pos (by have := i.isLt; omega)]
    simp [Block.get?, Block.length, show i.val - 3 < 1048573 by have := i.isLt; omega]
  ext k bound
  interval_cases k <;> simp only [TableData.rowNat, controlDecoder, Vector.getElem_map,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    Vector.getElem_replicate, Column.get?]
  all_goals exact column _ rfl

/-- Exact row equality is proved from the actual export and constructed public
    setup; it is never supplied as a premise to decoder soundness. -/
theorem native_exported_rows (i : Fin 1048576) :
    controlDecoder.row (p := mersenne31Modulus) i = setup.row i := by
  rcases i with ⟨n, bound⟩
  by_cases early : n < 3
  · interval_cases n <;> decide +kernel +revert
  · have tail := native_exported_tail ⟨n,bound⟩ (by simpa only [Fin.val_mk] using Nat.le_of_not_gt early)
    rw [TableData.row, tail]
    have absent : setup.slots[n]? = none := List.getElem?_eq_none (by simpa [setup] using Nat.le_of_not_gt early)
    simp [SparseDecoderSetup.row, absent]
    decide

/-- Actual exported membership transfers to the independently constructed public
    setup; accepted native equations exclude both the hole and complete tail. -/
theorem native_exported_source {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (member : ∃ i : Fin 1048576, decoderQuery w = controlDecoder.row i) :
    Fetched w before ∧ (w 13).val < 65536 ∧ (w 14).val < 65536 := by
  have logical : setup.table.Contains #[] (decoderQuery w) := by
    obtain ⟨i, same⟩ := member
    exact ⟨i, same.trans (native_exported_rows i)⟩
  exact public_decoder native_fixture_image holds logical

end Airbender.JumpBranchSlt.Proofs

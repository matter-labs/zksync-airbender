import Airbender.Proofs.SubwordMemory.NativeDecode
import Airbender.Proofs.Trace.StatefulDecoderSetup
import Airbender.Proofs.Tables.ConstantTail

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace Setup NativeSetup Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem native_words_0 (i : Fin 4) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (0 + i.val)))).read before =
      .ok (words[0 + i.val]'(by have := i.isLt; omega)) before := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,words,Std.ExtHashMap.getElem_insert]

private theorem native_words_1 (i : Fin 4) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (4 + i.val)))).read before =
      .ok (words[4 + i.val]'(by have := i.isLt; omega)) before := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,words,Std.ExtHashMap.getElem_insert]

private theorem native_words_2 (i : Fin 4) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (8 + i.val)))).read before =
      .ok (words[8 + i.val]'(by have := i.isLt; omega)) before := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,words,Std.ExtHashMap.getElem_insert]

private theorem native_words_3 (i : Fin 1) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (12 + i.val)))).read before =
      .ok (words[12 + i.val]'(by have := i.isLt; omega)) before := by
  fin_cases i
  simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,words,Std.ExtHashMap.getElem_insert]

theorem native_fixture_words (i : Fin 13) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * i.val))).read before = .ok words[i.val] before := by
  fin_cases i
  · exact native_words_0 ⟨0,by decide⟩
  · exact native_words_0 ⟨1,by decide⟩
  · exact native_words_0 ⟨2,by decide⟩
  · exact native_words_0 ⟨3,by decide⟩
  · exact native_words_1 ⟨0,by decide⟩
  · exact native_words_1 ⟨1,by decide⟩
  · exact native_words_1 ⟨2,by decide⟩
  · exact native_words_1 ⟨3,by decide⟩
  · exact native_words_2 ⟨0,by decide⟩
  · exact native_words_2 ⟨1,by decide⟩
  · exact native_words_2 ⟨2,by decide⟩
  · exact native_words_2 ⟨3,by decide⟩
  · exact native_words_3 ⟨0,by decide⟩

theorem native_fixture_slot (i : Fin 13) :
    programSlotRunWith SubwordMemory.decoderFields before (_root_.BitVec.ofNat 32 (4 * i.val)) =
      some (setup.slots[i.val]'(by change i.val < 13; exact i.isLt)) := by
  simp only [programSlotRunWith,native_fixture_words,native_fixture_decode,bind,Option.bind,pure]
  fin_cases i <;> rfl

theorem native_fixture_image : sparseDecoderSetupImage before 13 20 = some setup := by
  change (([0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48] : List (BitVec 32)).mapM
    (programSlotRunWith SubwordMemory.decoderFields before)).bind
      (fun slots => some (SparseDecoderSetup.mk slots 1048563)) = some setup
  simp only [List.mapM_cons,List.mapM_nil,
    show programSlotRunWith SubwordMemory.decoderFields before 0 = some (setup.slots[0]) from native_fixture_slot ⟨0,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 4 = some (setup.slots[1]) from native_fixture_slot ⟨1,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 8 = some (setup.slots[2]) from native_fixture_slot ⟨2,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 12 = some (setup.slots[3]) from native_fixture_slot ⟨3,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 16 = some (setup.slots[4]) from native_fixture_slot ⟨4,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 20 = some (setup.slots[5]) from native_fixture_slot ⟨5,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 24 = some (setup.slots[6]) from native_fixture_slot ⟨6,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 28 = some (setup.slots[7]) from native_fixture_slot ⟨7,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 32 = some (setup.slots[8]) from native_fixture_slot ⟨8,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 36 = some (setup.slots[9]) from native_fixture_slot ⟨9,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 40 = some (setup.slots[10]) from native_fixture_slot ⟨10,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 44 = some (setup.slots[11]) from native_fixture_slot ⟨11,by decide⟩,
    show programSlotRunWith SubwordMemory.decoderFields before 48 = some (setup.slots[12]) from native_fixture_slot ⟨12,by decide⟩,bind,Option.bind,pure]
  rfl

private theorem native_exported_column (j : Fin 10) :
    Setup.Proofs.constantTail 2147483646 12 nativeDecoder.columns[j.val].blocks.toList = true ∧
    (nativeDecoder.columns[j.val].blocks.toList.map Block.length).sum = 1048576 := by
  fin_cases j <;> decide +kernel +revert

/-- Every literal native tail cell, using symbolic compressed-block getters. -/
theorem native_exported_tail (i : Fin 1048576) (tail : 12 ≤ i.val) :
    nativeDecoder.rowNat i = Vector.replicate 10 2147483646 := by
  ext j bound
  have get := Setup.Proofs.constantTail_sound 2147483646 12
    nativeDecoder.columns[j].blocks.toList (native_exported_column ⟨j,bound⟩).1 i.val tail
    (by rw [(native_exported_column ⟨j,bound⟩).2]; exact i.isLt)
  simp only [TableData.rowNat,Vector.getElem_map,Vector.getElem_replicate,Column.get?]
  exact congrArg (fun value : Option Nat => value.getD 0) get

/-- All exported rows equal the independently constructed original public setup. -/
theorem native_exported_rows (i : Fin 1048576) :
    nativeDecoder.row (p := mersenne31Modulus) i = setup.row i := by
  rcases i with ⟨n,bound⟩
  by_cases early : n < 13
  · interval_cases n <;> decide +kernel +revert
  · rw [TableData.row,native_exported_tail ⟨n,bound⟩ (by change 12 ≤ n; omega)]
    have absent : setup.slots[n]? = none := List.getElem?_eq_none (by simpa [setup] using Nat.le_of_not_gt early)
    simp [SparseDecoderSetup.row,absent]
    decide

end Airbender.SubwordMemory.Proofs

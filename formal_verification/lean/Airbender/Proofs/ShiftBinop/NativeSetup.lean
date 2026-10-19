import Airbender.Review.Circuits.ShiftBinop.NativeData
import Airbender.Proofs.Trace.StatefulDecoderSetup
import Airbender.Proofs.Tables.ConstantTail
import Airbender.Proofs.Mersenne31

namespace Airbender.ShiftBinop.Proofs
open Trace Setup NativeSetup Reference.RiscV.Sail Reference.Sail

private theorem native_words_0 (i : Fin 5) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (0 + i.val)))).read before =
      .ok (words[0 + i.val]'(by have := i.isLt; omega)) before := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,words,Std.ExtHashMap.getElem_insert]

private theorem native_words_1 (i : Fin 5) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (5 + i.val)))).read before =
      .ok (words[5 + i.val]'(by have := i.isLt; omega)) before := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,words,Std.ExtHashMap.getElem_insert]

private theorem native_words_2 (i : Fin 5) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (10 + i.val)))).read before =
      .ok (words[10 + i.val]'(by have := i.isLt; omega)) before := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,words,Std.ExtHashMap.getElem_insert]

private theorem native_words_3 (i : Fin 5) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (15 + i.val)))).read before =
      .ok (words[15 + i.val]'(by have := i.isLt; omega)) before := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,words,Std.ExtHashMap.getElem_insert]

private theorem native_words_4 (i : Fin 5) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (20 + i.val)))).read before =
      .ok (words[20 + i.val]'(by have := i.isLt; omega)) before := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,words,Std.ExtHashMap.getElem_insert]

/-- Original byte reads for every public fixture word, split into small proofs. -/
theorem native_fixture_words (i : Fin 25) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * i.val))).read before = .ok words[i.val] before := by
  fin_cases i
  · exact native_words_0 ⟨0,by decide⟩
  · exact native_words_0 ⟨1,by decide⟩
  · exact native_words_0 ⟨2,by decide⟩
  · exact native_words_0 ⟨3,by decide⟩
  · exact native_words_0 ⟨4,by decide⟩
  · exact native_words_1 ⟨0,by decide⟩
  · exact native_words_1 ⟨1,by decide⟩
  · exact native_words_1 ⟨2,by decide⟩
  · exact native_words_1 ⟨3,by decide⟩
  · exact native_words_1 ⟨4,by decide⟩
  · exact native_words_2 ⟨0,by decide⟩
  · exact native_words_2 ⟨1,by decide⟩
  · exact native_words_2 ⟨2,by decide⟩
  · exact native_words_2 ⟨3,by decide⟩
  · exact native_words_2 ⟨4,by decide⟩
  · exact native_words_3 ⟨0,by decide⟩
  · exact native_words_3 ⟨1,by decide⟩
  · exact native_words_3 ⟨2,by decide⟩
  · exact native_words_3 ⟨3,by decide⟩
  · exact native_words_3 ⟨4,by decide⟩
  · exact native_words_4 ⟨0,by decide⟩
  · exact native_words_4 ⟨1,by decide⟩
  · exact native_words_4 ⟨2,by decide⟩
  · exact native_words_4 ⟨3,by decide⟩
  · exact native_words_4 ⟨4,by decide⟩

set_option maxRecDepth 32768 in
/-- Decode actual original instructions, retaining all original x0 forms. -/
theorem native_fixture_decode (i : Fin 25) :
    run (SailRV32.Functions.encdec_backwards words[i.val]) before = .ok instructions[i.val] before := by
  fin_cases i <;> with_unfolding_all rfl

/-- Public slot construction uses original byte reads/decoding, not exported
    values. The unsupported ADD slot is retained at its original location. -/
theorem native_fixture_slot (i : Fin 25) :
    programSlotRunWith decoderFields before (_root_.BitVec.ofNat 32 (4 * i.val)) =
      some (setup.slots[i.val]'(by change i.val < 25; exact i.isLt)) := by
  simp only [programSlotRunWith,native_fixture_words,native_fixture_decode,bind,Option.bind,pure]
  fin_cases i <;> rfl

/-- Exact original public construction of the full indexed padded setup. -/
theorem native_fixture_image : sparseDecoderSetupImage before 25 20 = some setup := by
  change (([0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96] : List (BitVec 32)).mapM
    (programSlotRunWith decoderFields before)).bind
      (fun slots => some (SparseDecoderSetup.mk slots 1048551)) = some setup
  simp only [List.mapM_cons,List.mapM_nil,
    show programSlotRunWith decoderFields before 0 = some (setup.slots[0]) from native_fixture_slot ⟨0,by decide⟩,
    show programSlotRunWith decoderFields before 4 = some (setup.slots[1]) from native_fixture_slot ⟨1,by decide⟩,
    show programSlotRunWith decoderFields before 8 = some (setup.slots[2]) from native_fixture_slot ⟨2,by decide⟩,
    show programSlotRunWith decoderFields before 12 = some (setup.slots[3]) from native_fixture_slot ⟨3,by decide⟩,
    show programSlotRunWith decoderFields before 16 = some (setup.slots[4]) from native_fixture_slot ⟨4,by decide⟩,
    show programSlotRunWith decoderFields before 20 = some (setup.slots[5]) from native_fixture_slot ⟨5,by decide⟩,
    show programSlotRunWith decoderFields before 24 = some (setup.slots[6]) from native_fixture_slot ⟨6,by decide⟩,
    show programSlotRunWith decoderFields before 28 = some (setup.slots[7]) from native_fixture_slot ⟨7,by decide⟩,
    show programSlotRunWith decoderFields before 32 = some (setup.slots[8]) from native_fixture_slot ⟨8,by decide⟩,
    show programSlotRunWith decoderFields before 36 = some (setup.slots[9]) from native_fixture_slot ⟨9,by decide⟩,
    show programSlotRunWith decoderFields before 40 = some (setup.slots[10]) from native_fixture_slot ⟨10,by decide⟩,
    show programSlotRunWith decoderFields before 44 = some (setup.slots[11]) from native_fixture_slot ⟨11,by decide⟩,
    show programSlotRunWith decoderFields before 48 = some (setup.slots[12]) from native_fixture_slot ⟨12,by decide⟩,
    show programSlotRunWith decoderFields before 52 = some (setup.slots[13]) from native_fixture_slot ⟨13,by decide⟩,
    show programSlotRunWith decoderFields before 56 = some (setup.slots[14]) from native_fixture_slot ⟨14,by decide⟩,
    show programSlotRunWith decoderFields before 60 = some (setup.slots[15]) from native_fixture_slot ⟨15,by decide⟩,
    show programSlotRunWith decoderFields before 64 = some (setup.slots[16]) from native_fixture_slot ⟨16,by decide⟩,
    show programSlotRunWith decoderFields before 68 = some (setup.slots[17]) from native_fixture_slot ⟨17,by decide⟩,
    show programSlotRunWith decoderFields before 72 = some (setup.slots[18]) from native_fixture_slot ⟨18,by decide⟩,
    show programSlotRunWith decoderFields before 76 = some (setup.slots[19]) from native_fixture_slot ⟨19,by decide⟩,
    show programSlotRunWith decoderFields before 80 = some (setup.slots[20]) from native_fixture_slot ⟨20,by decide⟩,
    show programSlotRunWith decoderFields before 84 = some (setup.slots[21]) from native_fixture_slot ⟨21,by decide⟩,
    show programSlotRunWith decoderFields before 88 = some (setup.slots[22]) from native_fixture_slot ⟨22,by decide⟩,
    show programSlotRunWith decoderFields before 92 = some (setup.slots[23]) from native_fixture_slot ⟨23,by decide⟩,
    show programSlotRunWith decoderFields before 96 = some (setup.slots[24]) from native_fixture_slot ⟨24,by decide⟩,bind,Option.bind,pure]
  rfl

private theorem native_exported_column (j : Fin 10) :
    Setup.Proofs.constantTail 2147483646 24 nativeDecoder.columns[j.val].blocks.toList = true ∧
    (nativeDecoder.columns[j.val].blocks.toList.map Block.length).sum = 1048576 := by
  fin_cases j <;> decide +kernel +revert

/-- Every actual exported tail cell is checked structurally from literal
    compressed blocks, without enumerating the million-row domain. -/
theorem native_exported_tail (i : Fin 1048576) (tail : 24 ≤ i.val) :
    nativeDecoder.rowNat i = Vector.replicate 10 2147483646 := by
  ext j bound
  have get := Setup.Proofs.constantTail_sound 2147483646 24
    nativeDecoder.columns[j].blocks.toList (native_exported_column ⟨j,bound⟩).1 i.val tail
    (by rw [(native_exported_column ⟨j,bound⟩).2]; exact i.isLt)
  simp only [TableData.rowNat,Vector.getElem_map,Vector.getElem_replicate,Column.get?]
  exact congrArg (fun value : Option Nat => value.getD 0) get

/-- Every native exported row equals the independently constructed public
    setup row, including the unsupported slot and the complete sentinel tail. -/
theorem native_exported_rows (i : Fin 1048576) :
    nativeDecoder.row (p := mersenne31Modulus) i = setup.row i := by
  rcases i with ⟨n,bound⟩
  by_cases early : n < 25
  · interval_cases n <;> decide +kernel +revert
  · rw [TableData.row,native_exported_tail ⟨n,bound⟩ (by change 24 ≤ n; omega)]
    have absent : setup.slots[n]? = none := List.getElem?_eq_none (by simpa [setup] using Nat.le_of_not_gt early)
    simp [SparseDecoderSetup.row,absent]
    decide

end Airbender.ShiftBinop.Proofs

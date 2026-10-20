import Tests.ShiftHistoryFixture
import Airbender.Review.Trace.Families.ShiftBinop.Values
import Airbender.Proofs.Sail.DecoderFrame

namespace Tests.ShiftValuesFixture
open Airbender Arithmetic Trace Verification ShiftBinop NativeSetup
open Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def before (sample : Fin 24) : State :=
  { NativeSetup.before with regs := (NativeSetup.before.regs
      |>.insert .x1 (0x8000ffff : BitVec 32) |>.insert .x2 (3 : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (BitVec.ofNat 32 (4 * sample.val))) }

private theorem native_words_0 (sample : Fin 24) (i : Fin 5) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (0 + i.val)))).read (before sample) =
      .ok (words[0 + i.val]'(by have := i.isLt; omega)) (before sample) := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,NativeSetup.before,words,Std.ExtHashMap.getElem_insert]

private theorem native_words_1 (sample : Fin 24) (i : Fin 5) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (5 + i.val)))).read (before sample) =
      .ok (words[5 + i.val]'(by have := i.isLt; omega)) (before sample) := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,NativeSetup.before,words,Std.ExtHashMap.getElem_insert]

private theorem native_words_2 (sample : Fin 24) (i : Fin 5) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (10 + i.val)))).read (before sample) =
      .ok (words[10 + i.val]'(by have := i.isLt; omega)) (before sample) := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,NativeSetup.before,words,Std.ExtHashMap.getElem_insert]

private theorem native_words_3 (sample : Fin 24) (i : Fin 5) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (15 + i.val)))).read (before sample) =
      .ok (words[15 + i.val]'(by have := i.isLt; omega)) (before sample) := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,NativeSetup.before,words,Std.ExtHashMap.getElem_insert]

private theorem native_words_4 (sample : Fin 24) (i : Fin 5) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * (20 + i.val)))).read (before sample) =
      .ok (words[20 + i.val]'(by have := i.isLt; omega)) (before sample) := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,NativeSetup.before,words,Std.ExtHashMap.getElem_insert]

/-- Original byte reads for every public fixture word, split into small proofs. -/
theorem native_fixture_words (sample : Fin 24) (i : Fin 25) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * i.val))).read (before sample) = .ok words[i.val] (before sample) := by
  fin_cases i
  · exact native_words_0 sample ⟨0,by decide⟩
  · exact native_words_0 sample ⟨1,by decide⟩
  · exact native_words_0 sample ⟨2,by decide⟩
  · exact native_words_0 sample ⟨3,by decide⟩
  · exact native_words_0 sample ⟨4,by decide⟩
  · exact native_words_1 sample ⟨0,by decide⟩
  · exact native_words_1 sample ⟨1,by decide⟩
  · exact native_words_1 sample ⟨2,by decide⟩
  · exact native_words_1 sample ⟨3,by decide⟩
  · exact native_words_1 sample ⟨4,by decide⟩
  · exact native_words_2 sample ⟨0,by decide⟩
  · exact native_words_2 sample ⟨1,by decide⟩
  · exact native_words_2 sample ⟨2,by decide⟩
  · exact native_words_2 sample ⟨3,by decide⟩
  · exact native_words_2 sample ⟨4,by decide⟩
  · exact native_words_3 sample ⟨0,by decide⟩
  · exact native_words_3 sample ⟨1,by decide⟩
  · exact native_words_3 sample ⟨2,by decide⟩
  · exact native_words_3 sample ⟨3,by decide⟩
  · exact native_words_3 sample ⟨4,by decide⟩
  · exact native_words_4 sample ⟨0,by decide⟩
  · exact native_words_4 sample ⟨1,by decide⟩
  · exact native_words_4 sample ⟨2,by decide⟩
  · exact native_words_4 sample ⟨3,by decide⟩
  · exact native_words_4 sample ⟨4,by decide⟩

theorem public_decode (sample : Fin 24) (i : Fin 25) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards words[i.val]) (before sample) =
      .ok instructions[i.val] (before sample) := by
  apply (Reference.Sail.decoded_misa_frame _ (ShiftBinop.Proofs.native_fixture_decode i)).2
  simp [before,Std.ExtDHashMap.get?_insert]

theorem public_slot (sample : Fin 24) (i : Fin 25) :
    programSlotRunWith ShiftBinop.decoderFields (before sample) (BitVec.ofNat 32 (4 * i.val)) =
      some (setup.slots[i.val]'(by change i.val < 25; exact i.isLt)) := by
  simp only [programSlotRunWith,native_fixture_words,public_decode,bind,Option.bind,pure]
  fin_cases i <;> rfl

theorem program_image (sample : Fin 24) : ShiftBinop.sparseDecoderSetupImage (before sample) 25 20 = some setup := by
  change (([0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96] : List (BitVec 32)).mapM
    (programSlotRunWith ShiftBinop.decoderFields (before sample))).bind
      (fun slots => some (SparseDecoderSetup.mk slots 1048551)) = some setup
  simp only [List.mapM_cons,List.mapM_nil,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 0 = some (setup.slots[0]) from public_slot sample ⟨0,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 4 = some (setup.slots[1]) from public_slot sample ⟨1,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 8 = some (setup.slots[2]) from public_slot sample ⟨2,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 12 = some (setup.slots[3]) from public_slot sample ⟨3,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 16 = some (setup.slots[4]) from public_slot sample ⟨4,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 20 = some (setup.slots[5]) from public_slot sample ⟨5,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 24 = some (setup.slots[6]) from public_slot sample ⟨6,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 28 = some (setup.slots[7]) from public_slot sample ⟨7,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 32 = some (setup.slots[8]) from public_slot sample ⟨8,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 36 = some (setup.slots[9]) from public_slot sample ⟨9,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 40 = some (setup.slots[10]) from public_slot sample ⟨10,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 44 = some (setup.slots[11]) from public_slot sample ⟨11,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 48 = some (setup.slots[12]) from public_slot sample ⟨12,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 52 = some (setup.slots[13]) from public_slot sample ⟨13,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 56 = some (setup.slots[14]) from public_slot sample ⟨14,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 60 = some (setup.slots[15]) from public_slot sample ⟨15,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 64 = some (setup.slots[16]) from public_slot sample ⟨16,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 68 = some (setup.slots[17]) from public_slot sample ⟨17,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 72 = some (setup.slots[18]) from public_slot sample ⟨18,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 76 = some (setup.slots[19]) from public_slot sample ⟨19,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 80 = some (setup.slots[20]) from public_slot sample ⟨20,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 84 = some (setup.slots[21]) from public_slot sample ⟨21,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 88 = some (setup.slots[22]) from public_slot sample ⟨22,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 92 = some (setup.slots[23]) from public_slot sample ⟨23,by decide⟩,
    show programSlotRunWith ShiftBinop.decoderFields (before sample) 96 = some (setup.slots[24]) from public_slot sample ⟨24,by decide⟩,bind,Option.bind,pure]
  rfl

theorem public_inputs (sample : Fin 24) :
    ImageBoundary (ShiftHistoryFixture.trace sample) (before sample)
      [.register 0,.register 1,.register 2,.register 3] := by
  have zero : (Cell.register 0).read (before sample) = .ok (0 : BitVec 32) (before sample) := rfl
  have first : (Cell.register 1).read (before sample) =
      .ok (0x8000ffff : BitVec 32) (before sample) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have second : (Cell.register 2).read (before sample) = .ok (3 : BitVec 32) (before sample) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have third : (Cell.register 3).read (before sample) = .ok (0 : BitVec 32) (before sample) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (before sample) =
      .ok (BitVec.ofNat 32 (4 * sample.val)) (before sample) := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero,first,second,third]
    rfl
  · rw [initialState,pc]
    fin_cases sample <;> rfl

theorem decoded (sample : Fin 24) :
    ShiftBinop.Decoded (ShiftHistoryFixture.trace sample) NativeSetup.setup := by
  intro row member
  have same : row = ShiftHistoryFixture.nativeRow sample := by simpa [ShiftHistoryFixture.trace] using member
  subst row
  rw [ShiftBinop.Proofs.row_decoder_query]
  simpa [ShiftBinop.decoderQuery,nativeDecoderQuery,importedConstraintsTraceColumns,
    importedConstraintsDecoderColumns,ShiftHistoryFixture.nativeRow,ShiftHistoryRows.assignment]
    using ShiftRouting.decoder_membership sample

end Tests.ShiftValuesFixture

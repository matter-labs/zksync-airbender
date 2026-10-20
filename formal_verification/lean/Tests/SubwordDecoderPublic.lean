import Tests.SubwordDecoderOriginal

namespace Tests.SubwordDecoderPublic
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordDecoderFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem fields (sample : Fin 7) : SubwordMemory.decoderFields (entry sample).instruction = some (entry sample).data := by
  fin_cases sample <;> rfl

theorem actual_bytes (sample : Fin 7) :
    (Cell.ram 0).read (before sample) = .ok (entry sample).bits (before sample) := by
  fin_cases sample <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,entry,Std.ExtHashMap.getElem_insert]

theorem original_decode (sample : Fin 7) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards (entry sample).bits) (before sample) =
      .ok (entry sample).instruction (before sample) := by
  have decoded : SailRV32.Functions.encdec_backwards (entry sample).bits = .pure (entry sample).instruction := by
    fin_cases sample
    · exact SubwordDecoderOriginal.decoded_0
    · exact SubwordDecoderOriginal.decoded_1
    · exact SubwordDecoderOriginal.decoded_2
    · exact SubwordDecoderOriginal.decoded_3
    · exact SubwordDecoderOriginal.decoded_4
    · exact SubwordDecoderOriginal.decoded_5
    · exact SubwordDecoderOriginal.decoded_6
  rw [decoded]
  rfl

theorem constructed (sample : Fin 7) : sparseDecoderSetupImage (before sample) 1 20 = some (setup sample) := by
  have slot : programSlotRunWith SubwordMemory.decoderFields (before sample) 0 = some (some (entry sample)) := by
    simp only [programSlotRunWith,actual_bytes,original_decode,bind,Option.bind,pure,fields,Option.map_some]
    fin_cases sample <;> rfl
  change (([0] : List (BitVec 32)).mapM (programSlotRunWith SubwordMemory.decoderFields (before sample))).bind
    (fun slots => some (SparseDecoderSetup.mk slots 1048575)) = some (setup sample)
  simp only [List.mapM_cons,List.mapM_nil,slot,bind,Option.bind,pure]
  rfl

theorem query (sample : Fin 7) : decoderQuery (assignment sample) = (entry sample).query := by
  fin_cases sample <;>
    simp only [SubwordMemory.decoderQuery,nativeDecoderQuery,importedConstraintsTraceColumns,
      importedConstraintsDecoderColumns,assignment,values,entry,Trace.ProgramEntry.query,Word.ofBitVec] <;>
    decide +kernel

theorem member (sample : Fin 7) :
    (setup sample).table.Contains #[] (decoderQuery (assignment sample)) := by
  rw [query]
  exact Airbender.Trace.Proofs.sparse_head_member (entry sample) [] 1048575

end Tests.SubwordDecoderPublic

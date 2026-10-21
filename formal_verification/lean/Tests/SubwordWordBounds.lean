import Airbender.Review.Trace.Families.SubwordMemory.Values
import Tests.SubwordBoundsFixture

namespace Tests.SubwordWordBounds
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordBoundsRows Tests.SubwordBoundsWitness Tests.SubwordBoundsFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def setup (sample : Fin 8) : SparseDecoderSetup Operation := ⟨[some (entry sample)],1048575⟩

theorem fields (sample : Fin 8) : SubwordMemory.decoderFields (entry sample).instruction = some (entry sample).data := by
  fin_cases sample <;> rfl

theorem actual_bytes (sample : Fin 8) :
    (Cell.ram 0).read (before sample) = .ok (entry sample).bits (before sample) := by
  fin_cases sample <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,entry,Tests.SubwordDecoderFixture.entry,Std.ExtHashMap.getElem_insert]

theorem original_decode (sample : Fin 8) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards (entry sample).bits) (before sample) =
      .ok (entry sample).instruction (before sample) := by
  have decoded : SailRV32.Functions.encdec_backwards (entry sample).bits = .pure (entry sample).instruction := by
    fin_cases sample
    · exact Tests.SubwordDecoderOriginal.decoded_0
    · exact Tests.SubwordDecoderOriginal.decoded_1
    · exact Tests.SubwordDecoderOriginal.decoded_2
    · exact Tests.SubwordDecoderOriginal.decoded_3
    · exact Tests.SubwordDecoderOriginal.decoded_4
    · exact Tests.SubwordDecoderOriginal.decoded_5
    · exact Tests.SubwordDecoderOriginal.decoded_6
    · rfl
  rw [decoded]
  rfl

theorem constructed (sample : Fin 8) : SubwordMemory.sparseDecoderSetupImage (before sample) 1 20 = some (setup sample) := by
  have slot : programSlotRunWith SubwordMemory.decoderFields (before sample) 0 = some (some (entry sample)) := by
    simp only [programSlotRunWith,actual_bytes,original_decode,bind,Option.bind,pure,fields,Option.map_some]
    fin_cases sample <;> rfl
  change (([0] : List (BitVec 32)).mapM (programSlotRunWith SubwordMemory.decoderFields (before sample))).bind
    (fun slots => some (SparseDecoderSetup.mk slots 1048575)) = some (setup sample)
  simp only [List.mapM_cons,List.mapM_nil,slot,bind,Option.bind,pure]
  rfl

theorem query (sample : Fin 8) : decoderQuery (assignment sample) = (entry sample).query := by
  fin_cases sample <;>
    simp only [SubwordMemory.decoderQuery,nativeDecoderQuery,importedConstraintsTraceColumns,
      importedConstraintsDecoderColumns,assignment,values0,values6,values7,
      Tests.SubwordHistoryRows.assignment,Tests.SubwordHistoryRows.aliasValues,
      Tests.SubwordDecoderFixture.assignment,Tests.SubwordDecoderFixture.values,
      entry,Tests.SubwordDecoderFixture.entry,Trace.ProgramEntry.query,Word.ofBitVec] <;>
    decide +kernel

theorem member (sample : Fin 8) : (setup sample).table.Contains #[] (decoderQuery (assignment sample)) := by
  rw [query]
  exact Airbender.Trace.Proofs.sparse_head_member (entry sample) [] 1048575

theorem decoded (sample : Fin 8) : Decoded (trace sample) (setup sample) := by
  intro actual present
  have same : actual = nativeRow sample := by simpa [trace] using present
  subst actual
  exact member sample

/-- All actual reads, writes and final words are derived in the same original
    public state that constructs the full sparse decoder and initialized image. -/
theorem public_bounds (sample : Fin 8) :
    (∀ actual ∈ (trace sample).rows, ∀ port ∈ actual.ports, (readToken actual.assignment port).word.Bounded) ∧
    (∀ actual ∈ (trace sample).rows, ∀ port ∈ actual.ports,
      (writeToken actual.columns actual.assignment port).word.Bounded) ∧
    (∀ token ∈ (trace sample).terminalMemory, token.word.Bounded) :=
  SubwordMemory.public_value_bounds (constructed sample) (public_inputs sample) (accepted sample) (decoded sample)

theorem actual_shadow_instruction :
    assignment ⟨0,by decide⟩ 32 = 33155 ∧ assignment ⟨6,by decide⟩ 32 = 49539 ∧
    assignment ⟨7,by decide⟩ 32 = 32899 ∧ assignment ⟨7,by decide⟩ 74 = 4 := by
  decide +kernel

end Tests.SubwordWordBounds

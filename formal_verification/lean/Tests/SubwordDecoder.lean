import Tests.SubwordDecoderPart0
import Tests.SubwordDecoderPart1
import Tests.SubwordDecoderPart2
import Tests.SubwordDecoderPart3
import Tests.SubwordDecoderPublic
import Tests.SubwordRouting

namespace Tests.SubwordDecoder
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordDecoderFixture Tests.SubwordDecoderPublic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem native_constraints (sample : Fin 7) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment sample)) (SubwordMemory.importedConstraints rom) := by
  fin_cases sample
  · exact SubwordDecoderPart0.accepted_0
  · exact SubwordDecoderPart0.accepted_1
  · exact SubwordDecoderPart1.accepted_2
  · exact SubwordDecoderPart1.accepted_3
  · exact SubwordDecoderPart2.accepted_4
  · exact SubwordDecoderPart2.accepted_5
  · exact SubwordDecoderPart3.accepted_6

/-- Both public claims apply to complete accepted native rows, with actual bytes. -/
theorem fetched (sample : Fin 7) : ∃ selected ∈ (setup sample).program,
    selected.SourceWith (before sample) SubwordMemory.decoderFields ∧ DecodedFields (assignment sample) selected :=
  native_fetched_fields (constructed sample) (native_constraints sample) (member sample)

theorem loads (sample : Fin 7) (load : assignment sample 12 = 0) :
    ∃ selected ∈ (setup sample).program,
      selected.SourceWith (before sample) SubwordMemory.decoderFields ∧
      DecodedFields (assignment sample) selected ∧ DecodedLoadWrites (assignment sample) selected :=
  native_fetched_load_writes (constructed sample) (native_constraints sample) (member sample) load

/-- The extra LBU case has different native lookup, candidate and actual write values. -/
theorem unsigned_byte : assignment ⟨6,by decide⟩ 56 = 1081598 ∧
    assignment ⟨6,by decide⟩ 60 = 254 ∧ assignment ⟨6,by decide⟩ 39 = 254 ∧
    assignment ⟨6,by decide⟩ 40 = 0 := by decide +kernel

theorem original_x0 : (entry ⟨3,by decide⟩).instruction = .LOAD (0,.Regidx 1,.Regidx 0,false,2) ∧
    assignment ⟨3,by decide⟩ 60 = 32769 ∧ assignment ⟨3,by decide⟩ 39 = 0 := by
  exact ⟨rfl,by decide +kernel⟩

/-- STORE retains its original instruction with unused rd zero and native zero flag one. -/
theorem store_flags : assignment ⟨4,by decide⟩ 7 = 0 ∧ assignment ⟨4,by decide⟩ 8 = 1 ∧
    assignment ⟨5,by decide⟩ 7 = 0 ∧ assignment ⟨5,by decide⟩ 8 = 1 := by decide +kernel

/-- Sign extension is preserved by the original projection, including both extremes. -/
theorem signed_immediates :
    SubwordMemory.decoderFields (.LOAD (4095,.Regidx 1,.Regidx 0,true,1)) =
      some ⟨.lbu,1,0,0,⟨65535,65535⟩,0,4⟩ ∧
    SubwordMemory.decoderFields (.STORE (2048,.Regidx 2,.Regidx 1,2)) =
      some ⟨.sh,1,2,0,⟨63488,65535⟩,1,1⟩ := by
  exact ⟨rfl,rfl⟩

theorem unsupported :
    SubwordMemory.decoderFields (.LOAD (0,.Regidx 1,.Regidx 3,false,4)) = none ∧
    SubwordMemory.decoderFields (.STORE (0,.Regidx 2,.Regidx 1,4)) = none ∧
    SubwordMemory.decoderFields (.LOAD (0,.Regidx 1,.Regidx 3,true,4)) = none := by decide +kernel

/-- No scan of the million-row padding tail is required for rejection. -/
theorem selected_query {w : Nat → ZMod mersenne31Modulus} (sample : Fin 7)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (SubwordMemory.importedConstraints rom))
    (membership : (setup sample).table.Contains #[] (decoderQuery w)) :
    decoderQuery w = (entry sample).query := by
  obtain ⟨selected,present,_,query⟩ := SubwordMemory.Proofs.fetched_sources (constructed sample) holds membership
  have same : selected = entry sample := by simpa [setup,SparseDecoderSetup.program] using present
  rwa [same] at query

/-- Old local rows are still accepted, but their unused load index was not decoded. -/
theorem old_load_index_rejected : ¬ (setup ⟨0,by decide⟩).table.Contains #[]
    (decoderQuery (Tests.SubwordRoutingFixture.assignment ⟨0,by decide⟩)) := by
  intro membership
  have query := selected_query ⟨0,by decide⟩ (Tests.SubwordRouting.native_constraints ⟨0,by decide⟩) membership
  have index := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[3]) query
  change (2 : ZMod mersenne31Modulus) = 0 at index
  exact (by decide +kernel : (2 : ZMod mersenne31Modulus) ≠ 0) index

theorem old_store_flag_rejected : ¬ (setup ⟨4,by decide⟩).table.Contains #[]
    (decoderQuery (Tests.SubwordRoutingFixture.assignment ⟨4,by decide⟩)) := by
  intro membership
  have query := selected_query ⟨4,by decide⟩ (Tests.SubwordRouting.native_constraints ⟨4,by decide⟩) membership
  have flag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) query
  change (0 : ZMod mersenne31Modulus) = 1 at flag
  exact (by decide +kernel : (0 : ZMod mersenne31Modulus) ≠ 1) flag

/-- Different supported public funct3/rd/operation rows cannot replace this fetch. -/
theorem crossed_unsigned_decoder_rejected : ¬ (setup ⟨0,by decide⟩).table.Contains #[]
    (decoderQuery (assignment ⟨6,by decide⟩)) := by
  intro membership
  have query := selected_query ⟨0,by decide⟩ (native_constraints ⟨6,by decide⟩) membership
  have funct := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[8]) query
  change (4 : ZMod mersenne31Modulus) = 0 at funct
  exact (by decide +kernel : (4 : ZMod mersenne31Modulus) ≠ 0) funct

theorem crossed_x0_decoder_rejected : ¬ (setup ⟨0,by decide⟩).table.Contains #[]
    (decoderQuery (assignment ⟨3,by decide⟩)) := by
  intro membership
  have query := selected_query ⟨0,by decide⟩ (native_constraints ⟨3,by decide⟩) membership
  have flag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) query
  change (1 : ZMod mersenne31Modulus) = 0 at flag
  exact (by decide +kernel : (1 : ZMod mersenne31Modulus) ≠ 0) flag

theorem crossed_store_decoder_rejected : ¬ (setup ⟨0,by decide⟩).table.Contains #[]
    (decoderQuery (assignment ⟨4,by decide⟩)) := by
  intro membership
  have query := selected_query ⟨0,by decide⟩ (native_constraints ⟨4,by decide⟩) membership
  have store := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change (1 : ZMod mersenne31Modulus) = 0 at store
  exact (by decide +kernel : (1 : ZMod mersenne31Modulus) ≠ 0) store

end Tests.SubwordDecoder

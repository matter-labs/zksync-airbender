import Airbender.Proofs.Reduced.PublicCallers
import Airbender.Proofs.FullUnsigned.TargetInputs
import Airbender.Proofs.Keccak.SplitCallerBridge

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail NativeDecoder
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- All six imported masks retain every field except unused funct3 slots. -/
theorem unrolled_full_mask_query [Fact p.Prime] (family : PooledFamily)
    (mask : ProgramRows.Mask) (binding : mask.columns = unrolledNativeMaskColumns family)
    {one two : Vector (ZMod p) 9}
    (omitted : family = .addSub ∨ family = .wordMemory ∨ family = .mulDiv ∨ family = .subwordMemory → one[7] = two[7])
    (equal : ProgramRows.maskRow mask one = ProgramRows.maskRow mask two) : one = two := by
  have eta (row : Vector (ZMod p) 9) :
      row = #v[row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7], row[8]] := by
    ext i bound
    interval_cases i <;> rfl
  rw [eta one, eta two] at equal
  cases family with
  | addSub | wordMemory | mulDiv | subwordMemory =>
    have slot := omitted (by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr rfl)))
    have shape : mask.columns = #[true, true, true, true, true, true, true, false, true] := binding
    have fields : one[0] = two[0] ∧ one[1] = two[1] ∧ one[2] = two[2] ∧
        one[3] = two[3] ∧ one[4] = two[4] ∧ one[5] = two[5] ∧ one[6] = two[6] ∧ one[8] = two[8] := by
      simpa [ProgramRows.maskRow, shape] using equal
    rcases fields with ⟨h0, h1, h2, h3, h4, h5, h6, h8⟩
    ext i bound
    interval_cases i <;> assumption
  | jumpBranchSlt | shiftBinop =>
    have shape : mask.columns = #[true, true, true, true, true, true, true, true, true] := binding
    have fields : one[0] = two[0] ∧ one[1] = two[1] ∧ one[2] = two[2] ∧
        one[3] = two[3] ∧ one[4] = two[4] ∧ one[5] = two[5] ∧ one[6] = two[6] ∧
        one[7] = two[7] ∧ one[8] = two[8] := by
      simpa [ProgramRows.maskRow, shape] using equal
    rcases fields with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
    ext i bound
    interval_cases i <;> assumption


/-- Every omitted full unsigned funct3 field is zero in the public registry. -/
theorem unrolled_full_dropped_funct3 {initial : State} {entry : PooledProgramEntry}
    (source : entry.SourceWith initial AddSub.Modular.External.decoderFields)
    (family : entry.data.family = .addSub ∨ entry.data.family = .wordMemory ∨
      entry.data.family = .mulDiv ∨ entry.data.family = .subwordMemory) : entry.data.funct3 = 0 := by
  rcases AddSub.Modular.External.Proofs.source_cases source with ⟨original, fields, rfl⟩ |
      ⟨original, _, equal⟩ | ⟨original, fields, equal⟩ | ⟨original, _, equal⟩ |
      ⟨original, fields, equal⟩
  · exact (arithmetic_public_properties fields.fields).1
  · simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simpa [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] using
      (MulDiv.Proofs.decoder_field_bounds fields.fields).2.2
  · simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simpa [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] using
      (SubwordMemory.Proofs.decoder_field_bounds fields.fields).2.2

/-- State matching bounds each incoming native PC without CPU-only RAM matching. -/
theorem unrolled_full_native_query_pc_low [Fact babyBearModulus.Prime]
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests) (initial : trace.initial.word.lo < limbBase) :
    ∀ row ∈ trace.rows, row.decoderQuery[0].val < 65536 := by
  intro row member
  have present : row.start ∈ trace.initial :: trace.rows.map Row.finish :=
    accepted.states.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩))
  have bound : row.start.word.lo < limbBase := by
    rcases List.mem_cons.mp present with same | written
    · simpa only [same] using initial
    · obtain ⟨previous, included, same⟩ := List.mem_map.mp written
      simpa only [same] using NativeDecoder.Proofs.pooled_final_pc_low (by decide) previous trace.rom
        (accepted.cpuEquations previous included)
  cases row with
  | mk family w =>
    cases family <;> change (w 0).val < 65536 at bound ⊢
    all_goals exact bound

end Airbender.Compiler.MachineTargets.Proofs

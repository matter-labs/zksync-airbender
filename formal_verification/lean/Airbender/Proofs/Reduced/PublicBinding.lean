import Airbender.Proofs.Reduced.SupportedExecution
import Airbender.Proofs.GKRProtocol.PublicAcceptedRows

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail NativeDecoder
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- The four imported masks retain every field except the unused funct3 slot. -/
theorem reduced_mask_query [Fact p.Prime] (family : PooledFamily)
    (allowed : AddSub.Modular.External.Caller.reducedFamily family = true)
    (mask : ProgramRows.Mask) (binding : mask.columns = unrolledNativeMaskColumns family)
    {one two : Vector (ZMod p) 9}
    (omitted : family = .addSub ∨ family = .wordMemory → one[7] = two[7])
    (equal : ProgramRows.maskRow mask one = ProgramRows.maskRow mask two) : one = two := by
  have eta (row : Vector (ZMod p) 9) :
      row = #v[row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7], row[8]] := by
    ext i bound
    interval_cases i <;> rfl
  rw [eta one, eta two] at equal
  cases family with
  | addSub | wordMemory =>
    have slot := omitted (by first | exact Or.inl rfl | exact Or.inr rfl)
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
  | mulDiv | subwordMemory => cases allowed

/-- The base arithmetic and word-memory metadata have no funct3 field. -/
theorem base_funct3_zero {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : Trace.decoderFields instruction = some data) : data.funct3 = 0 := by
  unfold Trace.decoderFields at fields
  split at fields
  case h_6 =>
    rename_i original imm rs1 rd
    change (if (rd : BitVec 5) = 0 then some (arithmeticFields 0 0 0 0 1)
      else some ⟨.wordMemory, rs1, 0, rd,
        Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩) = some data at fields
    split at fields
    all_goals cases fields
    · unfold arithmeticFields; split <;> rfl
    · rfl
  all_goals first
    | (cases fields; unfold arithmeticFields; split <;> rfl)
    | (cases fields; rfl)
    | (cases fields)

/-- Arithmetic, modular and external metadata clear the caller selector. -/
theorem arithmetic_public_properties {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : AddSub.Modular.External.arithmeticDecoderFields instruction = some data) :
    data.funct3 = 0 ∧ data.mask < 512 ∧ data.mask.testBit 7 = false := by
  have size := (AddSub.Modular.External.Proofs.field_bounds fields).2
  rcases AddSub.Modular.External.Proofs.arithmetic_cases fields with oracle | ⟨opcode, rs1, rs2, rd, _, rfl⟩
  · rcases NonDeterminism.Proofs.fields_cases oracle with standard | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · have small := (decoder_field_bounds standard).2
      refine ⟨base_funct3_zero standard, size, ?_⟩
      norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
      omega
    all_goals exact ⟨rfl, size, by norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]⟩
  · refine ⟨?_, size, ?_⟩
    all_goals unfold AddSub.Modular.nativeData arithmeticFields
    all_goals split <;> cases opcode <;>
      norm_num [AddSub.Modular.Opcode.selector, Nat.testBit, Nat.shiftRight_eq_div_pow]

/-- Only actual arithmetic metadata can produce an ordinary ADD/SUB row. -/
theorem stream_addsub_properties {initial : State} {entry : PooledProgramEntry}
    (source : entry.SourceWith initial AddSub.Modular.External.decoderFields)
    (family : entry.data.family = .addSub) :
    entry.data.funct3 = 0 ∧ entry.data.mask < 512 ∧ entry.data.mask.testBit 7 = false := by
  rcases AddSub.Modular.External.Proofs.source_cases source with ⟨original, fields, rfl⟩ |
      ⟨original, _, equal⟩ | ⟨original, _, equal⟩ | ⟨original, _, equal⟩ | ⟨original, _, equal⟩
  ·
    exact arithmetic_public_properties fields.fields
  all_goals simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family

/-- The omitted public slot is zero for both circuits that drop it. -/
theorem stream_dropped_funct3 {initial : State} {entry : PooledProgramEntry}
    (source : entry.SourceWith initial AddSub.Modular.External.decoderFields)
    (family : entry.data.family = .addSub ∨ entry.data.family = .wordMemory) : entry.data.funct3 = 0 := by
  rcases AddSub.Modular.External.Proofs.source_cases source with ⟨original, fields, rfl⟩ |
      ⟨original, _, equal⟩ | ⟨original, _, equal⟩ | ⟨original, _, equal⟩ | ⟨original, _, equal⟩
  ·
    exact (arithmetic_public_properties fields.fields).1
  all_goals simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family

/-- State matching bounds each incoming native PC without CPU-only RAM matching. -/
theorem reduced_native_query_pc_low [Fact babyBearModulus.Prime]
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers [] []) (initial : trace.initial.word.lo < limbBase) :
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

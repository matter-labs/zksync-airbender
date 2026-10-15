import Airbender.Review.Helpers.UnifiedReduced.Modular
import Airbender.Proofs.AddSub.ModularDecoder
import Airbender.Proofs.UnifiedReduced.MixedHistory

namespace Airbender.UnifiedReduced.Modular.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

theorem fields_cases {instruction : SailRV32.instruction} {data : DecoderData UnifiedFamily}
    (fields : Modular.decoderFields instruction = some data) :
    Mixed.decoderFields instruction = some data ∨ mopDecoderFields instruction = some data := by
  unfold Modular.decoderFields at fields
  cases old : Mixed.decoderFields instruction with
  | none => exact Or.inr (by simpa [old] using fields)
  | some original => exact Or.inl (by simpa [old] using fields)

theorem mop_cases {instruction : SailRV32.instruction} {data : DecoderData UnifiedFamily}
    (fields : mopDecoderFields instruction = some data) :
    ∃ opcode rs1 rs2 rd, instruction = AddSub.Modular.instruction opcode rs1 rs2 rd ∧
      data = mopData opcode rs1 rs2 rd := by
  unfold mopDecoderFields at fields
  split at fields
  · rename_i mop rs2 rs1 rd
    cases selected : AddSub.Modular.opcodeOfMop mop with
    | none => simp [selected] at fields
    | some opcode =>
      refine ⟨opcode, rs1, rs2, rd, ?_, ?_⟩
      · rw [AddSub.Modular.Proofs.mop_sound selected]; rfl
      · simpa [selected] using fields.symm
  · cases fields

theorem mop_bounds {instruction : SailRV32.instruction} {data : DecoderData UnifiedFamily}
    (fields : mopDecoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask < 524288 ∧ data.funct3 < 55 := by
  obtain ⟨opcode, rs1, rs2, rd, _, rfl⟩ := mop_cases fields
  unfold mopData AddSub.Modular.nativeData Trace.arithmeticFields DecoderData.mapFamily
  split
  · exact ⟨by constructor <;> decide, by decide, by decide⟩
  · exact ⟨Word.ofBitVec_bound 0,
      by change 2 ^ (opcode.selector - 10) < 524288; cases opcode <;> decide,
      by change 0 < 55; decide⟩

theorem mop_zero_cases {instruction : SailRV32.instruction} {data : DecoderData UnifiedFamily}
    (fields : mopDecoderFields instruction = some data) (zero : data.rd = 0) :
    data = ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ := by
  obtain ⟨opcode, rs1, rs2, rd, _, rfl⟩ := mop_cases fields
  change (AddSub.Modular.nativeData opcode rs1 rs2 rd).rd = 0 at zero
  rw [AddSub.Modular.Proofs.native_rd] at zero
  subst rd
  rfl

theorem mop_high_flags (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5) (i : Fin 12) :
    (mopData opcode rs1 rs2 rd).mask.testBit (7 + i.val) = false := by
  unfold mopData AddSub.Modular.nativeData Trace.arithmeticFields DecoderData.mapFamily
  split
  · change (1 : Nat).testBit (7 + i.val) = false
    fin_cases i <;> rfl
  · change (2 ^ (opcode.selector - 10)).testBit (7 + i.val) = false
    cases opcode <;> fin_cases i <;> rfl

theorem mop_metadata {entry : ProgramEntry} (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5)
    (fields : mopDecoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = AddSub.Modular.instruction opcode rs1 rs2 rd) :
    entry.data = mopData opcode rs1 rs2 rd := by
  rw [encoding] at fields
  cases opcode <;> simpa [mopDecoderFields, AddSub.Modular.instruction,
    AddSub.Modular.Opcode.mop, AddSub.Modular.opcodeOfMop] using fields.symm

theorem zero_preserving [Fact p.Prime] (hp : 524288 < p) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {initial : State} {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : Modular.programImage initial addresses = some program) (decoded : Decoded trace program) :
    ZeroPreserving trace := by
  intro row member
  cases row with
  | mk kind w =>
    cases kind
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
    obtain ⟨entry, present, _, query⟩ := decoder_member (decoded _ member)
    have source := run_program_sources image entry present
    rcases fields_cases source.fields with old | modular
    · rcases Mixed.Proofs.fields_cases old with standard | custom
      · have fetch : Fetched w initial := ⟨entry, ⟨source.bytes, source.decoded, standard⟩, query,
          UnifiedReduced.Proofs.decoder_selectors hp core
            (UnifiedReduced.Proofs.decoder_field_bounds standard).2.1 query⟩
        exact UnifiedReduced.Proofs.row_zero_preserving hp core (accepted.active _ member) fetch
      · exact UnifiedReduced.Proofs.custom_row_zero_preserving hp core custom query
    · exact UnifiedReduced.Proofs.row_zero_preserving_of_metadata hp core (accepted.active _ member)
        query (UnifiedReduced.Proofs.decoder_selectors hp core (mop_bounds modular).2.1 query)
        (fun zero => Or.inl (mop_zero_cases modular zero))

theorem memory_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : NativeInputs Modular.decoderFields trace initial cells program)
    (decoded : Decoded trace program) : MemoryExecution trace initial cells := by
  obtain ⟨addresses, image⟩ := inputs.programImage
  have zero := zero_preserving (by dsimp [timestampBase] at hp; omega) accepted image decoded
  exact native_row_history hp inverse accepted inputs.clocks inputs.image inputs.distinct inputs.aligned
    (zero_writes_of_preserving hp inverse accepted inputs.clocks inputs.image zero)

end Airbender.UnifiedReduced.Modular.Proofs

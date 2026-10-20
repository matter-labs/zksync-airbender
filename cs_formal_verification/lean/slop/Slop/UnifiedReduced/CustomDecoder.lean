import Slop.UnifiedReduced.Code

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem custom_field_bounds {instruction : SailRV32.instruction}
    {data : Trace.DecoderData Trace.UnifiedFamily}
    (fields : customDecoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask < 524288 ∧ data.funct3 < 55 := by
  cases instruction with
  | ZIMOP_MOP_RR value =>
    rcases value with ⟨mop, rs2, rs1, rd⟩
    cases rs2; cases rs1; cases rd
    simp only [customDecoderFields] at fields
    split at fields
    · cases fields
      change (⟨0, 0⟩ : Word).Bounded ∧ 512 < 524288 ∧ 0 < 55
      norm_num [Word.Bounded, limbBase]
    · cases fields
  | ZIMOP_MOP_R value =>
    rcases value with ⟨mop, rs1, rd⟩
    cases rs1; cases rd
    simp only [customDecoderFields] at fields
    split at fields
    · cases fields
    · cases found : customRotationTag mop with
      | none => simp only [found, bind, Option.bind] at fields; cases fields
      | some tag =>
        simp only [found, bind, Option.bind, Option.some.injEq] at fields
        subst data
        change (⟨0, 0⟩ : Word).Bounded ∧ 65536 < 524288 ∧ tag < 55
        refine ⟨by norm_num [Word.Bounded, limbBase], by decide, ?_⟩
        unfold customRotationTag at found
        split_ifs at found <;> cases found <;> decide
  | _ => cases fields

theorem custom_field_mask {instruction : SailRV32.instruction}
    {data : Trace.DecoderData Trace.UnifiedFamily}
    (fields : customDecoderFields instruction = some data) :
    data.mask = 512 ∨ data.mask = 65536 := by
  cases instruction with
  | ZIMOP_MOP_RR value =>
    rcases value with ⟨mop, rs2, rs1, rd⟩
    cases rs2; cases rs1; cases rd
    simp only [customDecoderFields] at fields
    split at fields
    · cases fields; exact Or.inl rfl
    · cases fields
  | ZIMOP_MOP_R value =>
    rcases value with ⟨mop, rs1, rd⟩
    cases rs1; cases rd
    simp only [customDecoderFields] at fields
    split at fields
    · cases fields
    · cases found : customRotationTag mop with
      | none => simp only [found, bind, Option.bind] at fields; cases fields
      | some tag =>
        simp only [found, bind, Option.bind, Option.some.injEq] at fields
        subst data
        exact Or.inr rfl
  | _ => cases fields

theorem custom_field_nonzero {instruction : SailRV32.instruction}
    {data : Trace.DecoderData Trace.UnifiedFamily}
    (fields : customDecoderFields instruction = some data) : data.rd ≠ 0 := by
  cases instruction with
  | ZIMOP_MOP_RR value =>
    rcases value with ⟨mop, rs2, rs1, rd⟩
    cases rs2; cases rs1; cases rd
    simp only [customDecoderFields] at fields
    split at fields
    · rename_i domain
      cases fields
      exact domain.2
    · cases fields
  | ZIMOP_MOP_R value =>
    rcases value with ⟨mop, rs1, rd⟩
    cases rs1; cases rd
    simp only [customDecoderFields] at fields
    split at fields
    · cases fields
    · rename_i nonzero
      cases found : customRotationTag mop with
      | none => simp only [found, bind, Option.bind] at fields; cases fields
      | some tag =>
        simp only [found, bind, Option.bind, Option.some.injEq] at fields
        subst data
        exact nonzero
  | _ => cases fields

theorem custom_fetched {p : Nat} [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    {before : State} {addresses : List (BitVec 32)} {program : List UnifiedReduced.ProgramEntry}
    (image : customProgramImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (member : (decoderTable program).Contains #[] (decoderQuery w)) :
    ∃ entry : UnifiedReduced.ProgramEntry, entry.SourceWith before customDecoderFields ∧
      decoderQuery w = entry.query ∧
      ∀ i : Fin 19, w importedConstraintsDecoderColumns.flags[i] =
        if entry.data.mask.testBit i.val then 1 else 0 := by
  obtain ⟨entry, present, _, query⟩ := Trace.Proofs.decoder_member member
  have source := Trace.Proofs.run_program_sources image entry present
  have bounds := custom_field_bounds source.fields
  exact ⟨entry, source, query, decoder_selectors hp h bounds.2.1 query⟩

theorem custom_source_after_history [Fact p.Prime] (hp : 131072 < p)
    {trace : UnifiedTrace p} (accepted : Accepted trace)
    {initial before : State} {cells : List Cell} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    {entry : UnifiedReduced.ProgramEntry} (source : entry.SourceWith initial customDecoderFields)
    (code : entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0) :
    entry.SourceWith before customDecoderFields :=
  entry_source_after_history past
    (fun event member pc inROM address => native_rom_unchanged hp accepted (native event member) pc inROM address)
    source code.1 code.2

end Airbender.UnifiedReduced.Proofs

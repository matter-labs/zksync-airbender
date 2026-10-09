import Airbender.Review.Trace.PooledProgram
import Airbender.Proofs.Trace.Program

namespace Airbender.Trace.Proofs

theorem mapped_query {Kind Target : Type} {p : Nat} (f : Kind → Target)
    (entry : ProgramEntry Kind) : (entry.mapFamily f).query (p := p) = entry.query := rfl

/-- Registry selection retains a successful original metadata projection. -/
theorem pooled_fields_cases {instruction : SailRV32.instruction} {data : DecoderData PooledFamily}
    (fields : pooledDecoderFields instruction = some data) :
    (∃ d, decoderFields instruction = some d ∧ data = d.mapFamily pooledArithmeticFamily) ∨
    (∃ d, JumpBranchSlt.decoderFields instruction = some d ∧ data = d.mapFamily (fun _ => .jumpBranchSlt)) ∨
    (∃ d, MulDiv.decoderFields instruction = some d ∧ data = d.mapFamily (fun _ => .mulDiv)) ∨
    (∃ d, ShiftBinop.decoderFields instruction = some d ∧ data = d.mapFamily (fun _ => .shiftBinop)) ∨
    (∃ d, SubwordMemory.decoderFields instruction = some d ∧ data = d.mapFamily (fun _ => .subwordMemory)) := by
  unfold pooledDecoderFields at fields
  cases a : decoderFields instruction
  · cases b : JumpBranchSlt.decoderFields instruction
    · cases c : MulDiv.decoderFields instruction
      · cases d : ShiftBinop.decoderFields instruction
        · cases e : SubwordMemory.decoderFields instruction
          · simp [a, b, c, d, e] at fields
          · rw [a, b, c, d, e] at fields
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl, (Option.some.inj fields).symm⟩)))
        · rw [a, b, c, d] at fields
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, (Option.some.inj fields).symm⟩)))
      · rw [a, b, c] at fields
        exact Or.inr (Or.inr (Or.inl ⟨_, rfl, (Option.some.inj fields).symm⟩))
    · rw [a, b] at fields
      exact Or.inr (Or.inl ⟨_, rfl, (Option.some.inj fields).symm⟩)
  · rw [a] at fields
    exact Or.inl ⟨_, rfl, (Option.some.inj fields).symm⟩

/-- Source evidence stays attached to the same public bytes and original Sail
    instruction; only the registry tag changes. -/
def PooledSource (before : Reference.RiscV.Sail.State) (entry : PooledProgramEntry)
    (arithmeticProjection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop :=
  (∃ e : ProgramEntry, e.SourceWith before arithmeticProjection ∧ entry = e.mapFamily pooledArithmeticFamily) ∨
  (∃ e : ProgramEntry Unit, e.SourceWith before JumpBranchSlt.decoderFields ∧
    entry = e.mapFamily (fun _ => .jumpBranchSlt)) ∨
  (∃ e : ProgramEntry Unit, e.SourceWith before MulDiv.decoderFields ∧
    entry = e.mapFamily (fun _ => .mulDiv)) ∨
  (∃ e : ProgramEntry Unit, e.SourceWith before ShiftBinop.decoderFields ∧
    entry = e.mapFamily (fun _ => .shiftBinop)) ∨
  (∃ e : ProgramEntry Unit, e.SourceWith before SubwordMemory.decoderFields ∧
    entry = e.mapFamily (fun _ => .subwordMemory))

theorem pooled_source_cases {before : Reference.RiscV.Sail.State} {entry : PooledProgramEntry}
    (source : entry.SourceWith before pooledDecoderFields) : PooledSource before entry := by
  obtain h | h | h | h | h := pooled_fields_cases source.fields
  all_goals obtain ⟨d, fields, equal⟩ := h
  · exact Or.inl ⟨⟨entry.pc, entry.bits, entry.instruction, d⟩,
      ⟨source.bytes, source.decoded, fields⟩, by cases entry; simp_all [ProgramEntry.mapFamily]⟩
  · exact Or.inr (Or.inl ⟨⟨entry.pc, entry.bits, entry.instruction, d⟩,
      ⟨source.bytes, source.decoded, fields⟩, by cases entry; simp_all [ProgramEntry.mapFamily]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨⟨entry.pc, entry.bits, entry.instruction, d⟩,
      ⟨source.bytes, source.decoded, fields⟩, by cases entry; simp_all [ProgramEntry.mapFamily]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨entry.pc, entry.bits, entry.instruction, d⟩,
      ⟨source.bytes, source.decoded, fields⟩, by cases entry; simp_all [ProgramEntry.mapFamily]⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨entry.pc, entry.bits, entry.instruction, d⟩,
      ⟨source.bytes, source.decoded, fields⟩, by cases entry; simp_all [ProgramEntry.mapFamily]⟩)))

end Airbender.Trace.Proofs

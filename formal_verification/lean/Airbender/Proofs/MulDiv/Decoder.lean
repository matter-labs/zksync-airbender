import Airbender.Review.MulDiv.Decoder
import Airbender.Proofs.Trace.Program
import Airbender.Proofs.MulDiv

namespace Airbender.MulDiv.Proofs
open Arithmetic

theorem decoder_field_bounds {instruction : SailRV32.instruction}
    {data : Trace.DecoderData Unit} (fields : decoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask < 16 ∧ data.funct3 = 0 := by
  unfold decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       simp [Word.Bounded, limbBase])

theorem decoder_selectors {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {w : Nat → ZMod p} {entry : ProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (small : entry.data.mask < 16) (query : decoderQuery w = entry.query) :
    ∀ i : Fin 4,
      w importedConstraintsDecoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0 := by
  let bits (i : Fin 4) := w importedConstraintsDecoderColumns.flags[i]
  have boolean : ∀ i, bits i = 0 ∨ bits i = 1 := by
    intro i
    have flag := (local_flags h).2 i
    fin_cases i <;> simpa [bits, importedConstraintsDecoderColumns] using flag
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) query
  change (∑ i : Fin 4, (2 ^ i.val : Nat) * bits i) = (entry.data.mask : ZMod p) at packed
  exact Trace.Proofs.unpack_decoder_bits_of_width (by dsimp [limbBase] at hp; omega)
    (by decide) (by omega) boolean packed

/-- Membership of the table constructed from public bytes fixes the actual
    decoder result and selectors; there is no assumed decoded instruction. -/
theorem fetched {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {w : Nat → ZMod p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before := by
  obtain ⟨entry, present, _, query⟩ := Trace.Proofs.decoder_member member
  have source := Trace.Proofs.run_program_sources image entry present
  have bounds := decoder_field_bounds source.fields
  exact ⟨entry, source, query, decoder_selectors hp h bounds.2.1 query⟩

end Airbender.MulDiv.Proofs

import Slop.Sail.ResetState
import Slop.Sail.Decoder
import Human.Circuits.JumpBranchSlt.Decoder
import Slop.Trace.Program
import Slop.JumpBranchSlt

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic

/-- Bounds are consequences of the metadata projection, not supplied per row. -/
theorem decoder_field_bounds {instruction : SailRV32.instruction}
    {data : Trace.DecoderData Unit} (fields : decoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask < 32 ∧ data.funct3 < 8 := by
  unfold decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       constructor
       · first | exact Word.ofBitVec_bound _ | (simp [Word.Bounded, limbBase])
       · constructor
         · dsimp
           decide
         · dsimp
           first | decide | (rename_i op; cases op <;> decide))

theorem decoder_selectors {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {w : Nat → ZMod p} {entry : ProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (small : entry.data.mask < 32) (query : decoderQuery w = entry.query) :
    ∀ i : Fin 5,
      w importedConstraintsDecoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0 := by
  let bits (i : Fin 5) := w importedConstraintsDecoderColumns.flags[i]
  have boolean : ∀ i, bits i = 0 ∨ bits i = 1 := by
    intro i
    have flag := (local_flags h).2 i
    fin_cases i <;> simpa [bits, importedConstraintsDecoderColumns] using flag
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) query
  change (∑ i : Fin 5, (2 ^ i.val : Nat) * bits i) = (entry.data.mask : ZMod p) at packed
  exact Trace.Proofs.unpack_decoder_bits_of_width (by dsimp [limbBase] at hp; omega)
    (by decide) (by omega) boolean packed

/-- Actual public fetch/decoding plus the imported Boolean equations fixes all
    native fields and selectors. No desired decoder result is an assumption. -/
theorem fetched {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {w : Nat → ZMod p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before := by
  obtain ⟨entry, present, _, query⟩ := Trace.Proofs.decoder_member member
  have source := Trace.Proofs.program_sources image entry present
  obtain ⟨immediate, mask, funct3⟩ := decoder_field_bounds source.fields
  exact ⟨entry, source, query, immediate, funct3, decoder_selectors hp h mask query⟩

/-- JAL and branch parity is derived from the actual Sail decoder and the
    metadata's sign extension, rather than supplied as a row assumption. -/
theorem decoder_offset_even {before : Reference.RiscV.Sail.State} {entry : ProgramEntry}
    (source : entry.SourceWith before decoderFields) :
    match entry.instruction with
    | .JAL _ | .BTYPE _ => entry.data.immediate.lo % 2 = 0
    | _ => True := by
  have decoded := Reference.Sail.decoded_offset_even entry.bits _ entry.instruction _
    (Reference.RiscV.Sail.decode_on_reset_run Reference.RiscV.Sail.configured_reset_machine source.decoded)
  have fields := source.fields
  cases kind : entry.instruction
  case JAL args =>
    rcases args with ⟨imm, rd⟩
    cases rd with
    | Regidx bits =>
      rw [kind] at fields decoded
      simp only [decoderFields] at fields
      split at fields
      all_goals rw [← Option.some.inj fields]
      all_goals exact Reference.Sail.sign_extend_low_even (by decide) imm decoded
  case BTYPE args =>
    rcases args with ⟨imm, rs2, rs1, op⟩
    cases rs2 with
    | Regidx right =>
      cases rs1 with
      | Regidx left =>
        rw [kind] at fields decoded
        simp only [decoderFields, Option.some.injEq] at fields
        rw [← fields]
        exact Reference.Sail.sign_extend_low_even (by decide) imm decoded
  all_goals trivial

end Airbender.JumpBranchSlt.Proofs

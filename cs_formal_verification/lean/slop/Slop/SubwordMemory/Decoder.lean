import Human.Circuits.SubwordMemory.Decoder
import Slop.Trace.Program
import Slop.SubwordMemory

namespace Airbender.SubwordMemory.Proofs
open Arithmetic

theorem decoder_field_bounds {instruction : SailRV32.instruction}
    {data : Trace.DecoderData Unit} (fields : decoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask < 8 ∧ data.funct3 = 0 := by
  unfold decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       exact ⟨Word.ofBitVec_bound _, by norm_num, rfl⟩)

theorem decoder_load_nonzero {instruction : SailRV32.instruction} {data : Trace.DecoderData Unit}
    (fields : decoderFields instruction = some data) (load : data.mask.testBit 0 = false) :
    data.rd ≠ 0 := by
  unfold decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try (simp only [Option.some.injEq] at fields; subst data)
  all_goals simp_all [Nat.testBit]

/-- Three native Boolean bits are uniquely fixed by the public packed mask. -/
theorem decoder_selectors {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} {entry : ProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (small : entry.data.mask < 8) (query : decoderQuery w = entry.query) :
    ∀ i : Fin 3,
      w importedConstraintsDecoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0 := by
  let bits (i : Fin 3) := w importedConstraintsDecoderColumns.flags[i]
  have boolean : ∀ i, bits i = 0 ∨ bits i = 1 := by
    intro i
    have flags := local_flags h
    fin_cases i
    · exact flags 1
    · exact flags 2
    · exact flags 3
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) query
  change (∑ i : Fin 3, (2 ^ i.val : Nat) * bits i) = (entry.data.mask : ZMod p) at packed
  exact Trace.Proofs.unpack_decoder_bits_of_width (by dsimp [limbBase] at hp; omega)
    (by decide) (by omega) boolean packed

theorem fetched {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (configuration : Reference.RiscV.Sail.Configured before)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before := by
  obtain ⟨entry, present, _, query⟩ := Trace.Proofs.decoder_member member
  have source := Trace.Proofs.run_program_sources image entry present
  exact ⟨entry, source, query, decoder_selectors hp h (decoder_field_bounds source.fields).2.1 query⟩

end Airbender.SubwordMemory.Proofs

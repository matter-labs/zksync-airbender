module
public import Human.Circuits.MulDiv.RVDecoder
public import Human.Circuits.MulDiv.Decoder
public import Slop.MulDiv
public import Slop.Trace.DecoderBits

@[expose] public section

/-! Native metadata facts of `MulDiv.rvDecoderFields` (twins of `Decoder.lean`/`Trace.lean` on `RV.Instr`). -/

namespace Airbender.MulDiv.Proofs
open Arithmetic

theorem rv_decoder_field_bounds {i : RV.Instr} {data : Trace.DecoderData Unit}
    (fields : rvDecoderFields i = some data) :
    data.immediate.Bounded ∧ data.mask < 16 ∧ data.funct3 = 0 := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       simp [Word.Bounded, limbBase])

theorem rv_decoder_nonzero_destination {i : RV.Instr} {data : Trace.DecoderData Unit}
    (fields : rvDecoderFields i = some data) : data.rd ≠ 0 := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try (simp only [Option.some.injEq] at fields; subst data)
  all_goals simp_all

theorem rv_decoder_selectors {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {w : Nat → ZMod p} {entry : RVProgramEntry}
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

end Airbender.MulDiv.Proofs

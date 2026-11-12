module
public import Human.Circuits.ShiftBinop.RVDecoder
public import Slop.ShiftBinop
public import Slop.Trace.DecoderBits

@[expose] public section

/-! Native metadata facts of `ShiftBinop.rvDecoderFields` (twins of `Decoder.lean`/`Trace.lean` on `RV.Instr`). -/

namespace Airbender.ShiftBinop.Proofs
open Arithmetic

theorem rv_decoder_field_bounds {i : RV.Instr} {data : Trace.DecoderData Unit}
    (fields : rvDecoderFields i = some data) :
    data.immediate.Bounded ∧ data.mask < 4 ∧ data.funct3 < 8 := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try simp only [instructionFields] at fields
  all_goals try split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       simp [Operation.isShift, Operation.tag, Word.Bounded, limbBase, binaryImmediate]
       all_goals omega)

/-- Public decoding admits exactly the native binary or shift operation tags. -/
theorem rv_decoder_operation_tags {i : RV.Instr} {data : Trace.DecoderData Unit}
    (fields : rvDecoderFields i = some data) :
    (data.mask = 1 ∧ (data.funct3 = 1 ∨ data.funct3 = 2 ∨ data.funct3 = 3 ∨ data.funct3 = 5)) ∨
      (data.mask = 2 ∧ (data.funct3 = 4 ∨ data.funct3 = 6 ∨ data.funct3 = 7)) := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try simp only [instructionFields] at fields
  all_goals try split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       simp [Operation.isShift, Operation.tag])

theorem rv_decoder_nonzero_destination {i : RV.Instr} {data : Trace.DecoderData Unit}
    (fields : rvDecoderFields i = some data) : data.rd ≠ 0 := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try simp only [instructionFields] at fields
  all_goals try split at fields
  all_goals try (simp only [Option.some.injEq] at fields; subst data)
  all_goals simp_all

theorem rv_decoder_selectors {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {w : Nat → ZMod p} {entry : RVProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (small : entry.data.mask < 4) (query : decoderQuery w = entry.query) :
    ∀ i : Fin 2,
      w importedConstraintsDecoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0 := by
  let bits (i : Fin 2) := w importedConstraintsDecoderColumns.flags[i]
  have boolean : ∀ i, bits i = 0 ∨ bits i = 1 := by
    intro i
    have flag := (local_flags h).2 i
    fin_cases i <;> simpa [bits, importedConstraintsDecoderColumns] using flag
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) query
  change (∑ i : Fin 2, (2 ^ i.val : Nat) * bits i) = (entry.data.mask : ZMod p) at packed
  exact Trace.Proofs.unpack_decoder_bits_of_width (by dsimp [limbBase] at hp; omega)
    (by decide) (by omega) boolean packed

end Airbender.ShiftBinop.Proofs

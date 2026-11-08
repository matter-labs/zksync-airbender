module
public import Human.Circuits.JumpBranchSlt.RVDecoder
public import Human.Circuits.JumpBranchSlt.Decoder
public import Slop.JumpBranchSlt
public import Slop.Trace.DecoderBits

@[expose] public section

/-! Native metadata facts of `JumpBranchSlt.rvDecoderFields` (twins of `Decoder.lean`/`Trace.lean` on `RV.Instr`). -/

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic

theorem rvFunct3_lt (cond : RV.Cond) : Branch.rvFunct3 cond < 8 := by
  cases cond <;> decide

theorem rv_decoder_field_bounds {i : RV.Instr} {data : Trace.DecoderData Unit}
    (fields : rvDecoderFields i = some data) :
    data.immediate.Bounded ∧ data.mask < 32 ∧ data.funct3 < 8 := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       refine ⟨?_, ?_, ?_⟩
       · first | exact Word.ofBitVec_bound _ | (simp [Word.Bounded, limbBase])
       · dsimp
         first | decide | (split <;> decide)
       · dsimp
         first | decide | exact rvFunct3_lt _)

/-- The masks admitted by the decoder: JAL/JALR (1, 2, or 17, 18 for x0), comparison (4), branch (24). -/
theorem rv_decoder_masks {i : RV.Instr} {data : Trace.DecoderData Unit}
    (fields : rvDecoderFields i = some data) :
    data.mask = 1 ∨ data.mask = 2 ∨ data.mask = 4 ∨
      data.mask = 17 ∨ data.mask = 18 ∨ data.mask = 24 := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try (simp only [Option.some.injEq] at fields; subst data)
  all_goals first
    | (solve | cases fields)
    | simp

/-- An x0 destination is the native discarded-write branch (`mask` bit 4). -/
theorem rv_decoder_zero_discarded {i : RV.Instr} {data : Trace.DecoderData Unit}
    (fields : rvDecoderFields i = some data) (zero : data.rd = 0) : data.mask.testBit 4 = true := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try (simp only [Option.some.injEq] at fields; subst data)
  all_goals first
    | (solve | cases fields)
    | ((try simp_all) <;> decide)

theorem rv_decoder_selectors {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {w : Nat → ZMod p} {entry : RVProgramEntry}
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

end Airbender.JumpBranchSlt.Proofs

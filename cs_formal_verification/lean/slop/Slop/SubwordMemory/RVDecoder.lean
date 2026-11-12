module
public import Human.Circuits.SubwordMemory.RVDecoder
public import Human.Circuits.SubwordMemory.Decoder
public import Slop.SubwordMemory
public import Slop.Trace.DecoderBits

@[expose] public section

/-! Native metadata facts of `SubwordMemory.rvDecoderFields` (twins of `Decoder.lean` on `RV.Instr`). -/

namespace Airbender.SubwordMemory.Proofs
open Arithmetic

theorem rv_decoder_field_bounds {i : RV.Instr} {data : Trace.DecoderData Unit}
    (fields : rvDecoderFields i = some data) :
    data.immediate.Bounded ∧ data.mask < 8 ∧ data.funct3 = 0 := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       exact ⟨Word.ofBitVec_bound _, by norm_num, rfl⟩)

theorem rv_decoder_load_nonzero {i : RV.Instr} {data : Trace.DecoderData Unit}
    (fields : rvDecoderFields i = some data) (load : data.mask.testBit 0 = false) :
    data.rd ≠ 0 := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try (simp only [Option.some.injEq] at fields; subst data)
  all_goals simp_all [Nat.testBit]

/-- Three native Boolean bits are uniquely fixed by the public packed mask. -/
theorem rv_decoder_selectors {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} {entry : RVProgramEntry}
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

end Airbender.SubwordMemory.Proofs

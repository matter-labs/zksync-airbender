module
public import Proven.UnifiedReduced.RV.Arith
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section
namespace Airbender.UnifiedReduced.Modular.Proofs
open Arithmetic Trace Trace.Proofs UnifiedReduced.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Low arithmetic metadata uses the native register ports and the ordinary PC successor without an ordinary-instruction premise. -/
theorem row_frame {setup : Table (ZMod babyBearModulus) (fields 10)} {w : Nat → ZMod babyBearModulus}
    {cells : List Cell} {epoch : Nat} {before after : _root_.RV.State} {entry : RVProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) (query : decoderQuery w = entry.query) (small : entry.data.mask < 512)
    (pc : before.pc = entry.pc)
    (history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)).reverse before after) :
    (∀ k : Fin 19, w (11 + k.val) = if entry.data.mask.testBit k.val then 1 else 0) ∧
      w 20 = 0 ∧
      before.getReg entry.data.rs1 = (Word.mk (w 36).val (w 37).val).toBitVec ∧
      before.getReg entry.data.rs2 = (Word.mk (w 42).val (w 43).val).toBitVec ∧
      before.getReg entry.data.rd = (Word.mk (w 48).val (w 49).val).toBitVec ∧
      _root_.RV.Same after (before.setReg entry.data.rd (Word.mk (w 50).val (w 51).val).toBitVec) ∧
      (Word.mk (w 30).val (w 31).val).toBitVec = before.pc + 4 := by
  have flags := RV.mask_column (RV.rv_decoder_selectors (by decide) core (by omega) query)
  have high (k : Fin 19) (large : 9 ≤ k.val) : w (11 + k.val) = 0 := by
    have power : (512 : Nat) ≤ 2 ^ k.val :=
      calc (512 : Nat) = 2 ^ 9 := by norm_num
        _ ≤ 2 ^ k.val := Nat.pow_le_pow_right (by norm_num) large
    rw [flags k, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le small power)]
    rfl
  have indices := rv_native_query_indices (by decide : limbBase < babyBearModulus) query
  have reads := RV.rv_register_reads (by decide) core (high 17 (by decide)) query epoch history
  have written := RV.rv_register_write core (high 18 (by decide)) indices.2.2 epoch history
  have low := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[0]) query
  have upper := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[1]) query
  change w 0 = ((Word.ofBitVec entry.pc).lo : ZMod babyBearModulus) at low
  change w 1 = ((Word.ofBitVec entry.pc).hi : ZMod babyBearModulus) at upper
  have successor := pc_successor (by decide) core active
    ⟨high 10 (by decide), high 11 (by decide), high 12 (by decide), high 13 (by decide)⟩
    (initial := Word.ofBitVec entry.pc) (final := Word.mk (w 30).val (w 31).val)
    ⟨low, upper, rfl, rfl⟩ (Word.ofBitVec_bound _)
  refine ⟨flags, high 9 (by decide), reads.1, reads.2, written.1, written.2, ?_⟩
  rw [successor.2.2, Word.ofBitVec_roundtrip, pc]

end Airbender.UnifiedReduced.Modular.Proofs

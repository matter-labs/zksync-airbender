module
public import Human.Circuits.SubwordMemory.RVModel
public import Slop.Trace.DecoderBits
public import Slop.Trace.RVPooledRow
public import Slop.SubwordMemory

@[expose] public section

/-! Native decoder metadata of the RV subword row's instruction (`SubwordMemory.rvDecoderFields`, through the pooled
    registry `rvPooledDecoderFields`), and what a matching decoder query fixes in the row: the store/byte/sign
    selectors, PC limbs, immediate limbs and register indices. No Sail term: the projection is a function of
    `RV.Instr`. -/

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace

/-- The decoder data of `rvInstruction input` (`SubwordMemory.rvDecoderFields`; load destination not x0). -/
def rvData (input : RVInput) : DecoderData Unit :=
  ⟨(), input.rs1, if input.store then input.rs2 else 0, if input.store then 0 else input.rd,
    Word.ofBitVec (input.encodedImmediate.signExtend 32),
    (if input.store then 1 else 0) + (if input.byte then 2 else 0) + (if input.signed && !input.store then 4 else 0),
    0⟩

/-- A subword entry of the pooled registry for `rvInstruction input` has the row's data; the registry routes loads to
    x0 elsewhere (`rvDecoderFields` rejects them), so a subword load has `rd ≠ x0`. -/
theorem rv_pooled_fields {input : RVInput} {data : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields (rvInstruction input) = some data) (family : data.family = .subwordMemory) :
    (input.store = false → input.rd ≠ 0) ∧ data = (rvData input).mapFamily (fun _ => .subwordMemory) := by
  obtain ⟨d, fd, rfl⟩ := (Trace.Proofs.rv_pooled_fields_family fields).2.2.2.2 family
  cases hs : input.store <;> cases hb : input.byte <;> cases hg : input.signed
  all_goals by_cases hz : input.rd = 0
  all_goals simp only [rvInstruction, rvDecoderFields, hs, hb, hg, hz, Bool.false_eq_true, ite_false, ite_true,
    Option.some.injEq, reduceCtorEq] at fd
  all_goals first
    | (subst fd; exact ⟨fun _ => hz, by simp [rvData, hs, hb, hg]⟩)
    | (subst fd; exact ⟨by simp, by simp [rvData, hs, hb, hg]⟩)

/-- A decoder query matching an entry with the row's data fixes the three selectors, the start PC limbs, the
    immediate limbs and the register indices the row uses. -/
theorem rv_query_facts {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) {w : Nat → ZMod p}
    {setup : Table (ZMod p) (fields 9)}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    {input : RVInput} {entry : RVPooledProgramEntry}
    (data : entry.data = (rvData input).mapFamily (fun _ => .subwordMemory))
    (query : (⟨.subwordMemory, w⟩ : Row p PooledFamily).decoderQuery = entry.query) :
    w 10 = (if input.store then 1 else 0) ∧ w 11 = (if input.byte then 1 else 0) ∧
    (input.store = false → w 12 = if input.signed then 1 else 0) ∧
    (⟨(w 0).val, (w 1).val⟩ : Word) = Word.ofBitVec entry.pc ∧
    (⟨(w 8).val, (w 9).val⟩ : Word) = Word.ofBitVec (input.encodedImmediate.signExtend 32) ∧
    w 5 = (input.rs1.toNat : ZMod p) ∧
    (input.store = true → w 6 = (input.rs2.toNat : ZMod p)) ∧
    (input.store = false → w 7 = (input.rd.toNat : ZMod p)) := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have q (k : Fin 9) := congrArg (fun v : Vector (ZMod p) 9 => v[k]) query
  have q0 := q 0
  have q1 := q 1
  have q2 := q 2
  have q3 := q 3
  have q4 := q 4
  have q5 := q 5
  have q6 := q 6
  have q8 := q 8
  change w 0 = ((Word.ofBitVec entry.pc).lo : ZMod p) at q0
  change w 1 = ((Word.ofBitVec entry.pc).hi : ZMod p) at q1
  change w 5 = (entry.data.rs1.toNat : ZMod p) at q2
  change w 6 = (entry.data.rs2.toNat : ZMod p) at q3
  change w 7 = (entry.data.rd.toNat : ZMod p) at q4
  change w 8 = (entry.data.immediate.lo : ZMod p) at q5
  change w 9 = (entry.data.immediate.hi : ZMod p) at q6
  change (∑ i : Fin 3, (2 ^ i.val : Nat) * w #[10, 11, 12][i]) = (entry.data.mask : ZMod p) at q8
  rw [data] at q2 q3 q4 q5 q6 q8
  have boolean : ∀ i : Fin 3, w #[10, 11, 12][i] = 0 ∨ w #[10, 11, 12][i] = 1 := by
    intro i
    fin_cases i
    · exact local_flags h 1
    · exact local_flags h 2
    · exact local_flags h 3
  have small : ((rvData input).mapFamily (fun _ => PooledFamily.subwordMemory)).mask < 512 := by
    cases hs : input.store <;> cases hb : input.byte <;> cases hg : input.signed <;>
      simp [rvData, DecoderData.mapFamily, hs, hb, hg]
  have bits := Trace.Proofs.unpack_decoder_bits_of_width (by omega) (by decide) small boolean q8
  have b0 := bits 0
  have b1 := bits 1
  have b2 := bits 2
  refine ⟨?_, ?_, ?_, ?_, ?_, q2, ?_, ?_⟩
  · cases hs : input.store <;> cases hb : input.byte <;> cases hg : input.signed <;>
      simpa [rvData, DecoderData.mapFamily, hs, hb, hg, Nat.testBit] using b0
  · cases hs : input.store <;> cases hb : input.byte <;> cases hg : input.signed <;>
      simpa [rvData, DecoderData.mapFamily, hs, hb, hg, Nat.testBit] using b1
  · intro hs
    cases hb : input.byte <;> cases hg : input.signed <;>
      simpa [rvData, DecoderData.mapFamily, hs, hb, hg, Nat.testBit] using b2
  · have bound := Word.ofBitVec_bound entry.pc
    rw [q0, q1, ZMod.val_natCast_of_lt (lt_trans bound.1 limbSize),
      ZMod.val_natCast_of_lt (lt_trans bound.2 limbSize)]
  · have bound := Word.ofBitVec_bound (input.encodedImmediate.signExtend 32)
    change w 8 = ((Word.ofBitVec (input.encodedImmediate.signExtend 32)).lo : ZMod p) at q5
    change w 9 = ((Word.ofBitVec (input.encodedImmediate.signExtend 32)).hi : ZMod p) at q6
    rw [q5, q6, ZMod.val_natCast_of_lt (lt_trans bound.1 limbSize),
      ZMod.val_natCast_of_lt (lt_trans bound.2 limbSize)]
  · intro hs
    simpa [rvData, DecoderData.mapFamily, hs] using q3
  · intro hs
    simpa [rvData, DecoderData.mapFamily, hs] using q4

end Airbender.SubwordMemory.Proofs

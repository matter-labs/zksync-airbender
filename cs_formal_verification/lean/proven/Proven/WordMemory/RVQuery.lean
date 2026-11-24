module
public import Human.Circuits.WordMemory.RVModel
public import Proven.Trace.RVPooledRow

@[expose] public section

/-! Native decoder metadata of the RV LW/SW row's instruction (`Trace.rvDecoderFields`, through the pooled registry
    `rvPooledDecoderFields`), and what a matching decoder query fixes in the row: the store selector, PC limbs,
    immediate limbs and register indices. No Sail term: the projection is a function of `RV.Instr`. -/

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace

/-- The decoder data of `rvInstruction input` (`Trace.rvDecoderFields`; LW destination not x0). -/
def rvData (input : RVInput) : DecoderData :=
  ⟨.wordMemory, input.rs1, if input.store then input.rs2 else 0, if input.store then 0 else input.rd,
    Word.ofBitVec (input.encodedImmediate.signExtend 32), if input.store then 1 else 0, 0⟩

/-- A word-memory entry of the pooled registry for `rvInstruction input` has the row's data; an LW to x0 is an ADD/SUB
    NOP (family `.addSub`), so a word-memory LW has `rd ≠ x0`. -/
theorem rv_word_fields {input : RVInput} {data : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields (rvInstruction input) = some data) (family : data.family = .wordMemory) :
    (input.store = false → input.rd ≠ 0) ∧ data = (rvData input).mapFamily pooledArithmeticFamily := by
  obtain ⟨d, fd, rfl⟩ := (Trace.Proofs.rv_pooled_fields_family fields).1 (Or.inr family)
  cases hs : input.store
  · by_cases hz : input.rd = 0
    · simp only [rvInstruction, hs, Bool.false_eq_true, ite_false, rvDecoderFields, hz, ite_true,
        Option.some.injEq] at fd
      subst fd
      simp [arithmeticFields, DecoderData.mapFamily, pooledArithmeticFamily] at family
    · simp only [rvInstruction, hs, Bool.false_eq_true, ite_false, rvDecoderFields, hz,
        Option.some.injEq] at fd
      subst fd
      exact ⟨fun _ => hz, by simp [rvData, hs]⟩
  · simp only [rvInstruction, hs, ite_true, rvDecoderFields, Option.some.injEq] at fd
    subst fd
    exact ⟨by simp, by simp [rvData, hs]⟩

/-- A decoder query matching an entry with the row's data fixes the store selector, the start PC limbs, the
    immediate limbs and the register indices the row uses. -/
theorem rv_query_facts {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) {w : Nat → ZMod p}
    {input : RVInput} {entry : RVPooledProgramEntry}
    (data : entry.data = (rvData input).mapFamily pooledArithmeticFamily)
    (query : (⟨.wordMemory, w⟩ : Row p PooledFamily).decoderQuery = entry.query) :
    w 10 = (if input.store then 1 else 0) ∧
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
  change (∑ i : Fin 1, (2 ^ i.val : Nat) * w #[10][i]) = (entry.data.mask : ZMod p) at q8
  rw [data] at q2 q3 q4 q5 q6 q8
  refine ⟨?_, ?_, ?_, q2, ?_, ?_⟩
  · cases hs : input.store <;> simpa [rvData, DecoderData.mapFamily, hs] using q8
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

end Airbender.WordMemory.Proofs

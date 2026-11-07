import Human.Circuits.MulDiv.RVModel
import Slop.Trace.DecoderBits
import Slop.MulDiv
import Slop.MulDiv.RVResult

/-! Native decoder metadata of the RV MulDiv row's instruction (`MulDiv.rvDecoderFields`, through the pooled
    registry `rvPooledDecoderFields`), and what a matching decoder query fixes in the row: selectors, PC limbs and
    register indices. No Sail term: the projection is a function of `RV.Instr`. -/

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace

/-- The decoder data of `rvInstruction input` (`MulDiv.rvDecoderFields`, destination not x0). -/
def rvData (input : RVInput) : DecoderData Unit :=
  ⟨(), input.rs1, input.rs2, input.rd, ⟨0, 0⟩, 2 ^ input.operation.selector.val, 0⟩

/-- The pooled registry routes the four RV MUL/DIV instructions to this family only when `rd ≠ x0`
    (x0 destinations are ADD/SUB-family NOP rows, excluded by the family tag). -/
theorem rv_pooled_fields {input : RVInput} {data : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields (rvInstruction input) = some data) (family : data.family = .mulDiv) :
    input.rd ≠ 0 ∧ data = (rvData input).mapFamily (fun _ => .mulDiv) := by
  obtain ⟨operation, left, right, pc, rs1, rs2, rd, before⟩ := input
  by_cases hz : rd = 0
  · subst hz
    cases operation <;> simp [rvPooledDecoderFields, rvInstruction, Trace.rvDecoderFields] at fields <;>
      (subst fields; simp [DecoderData.mapFamily, pooledArithmeticFamily, arithmeticFields] at family)
  · refine ⟨hz, ?_⟩
    have nz : rd ≠ 0#5 := hz
    cases operation <;>
      simp [rvPooledDecoderFields, rvInstruction, Trace.rvDecoderFields, JumpBranchSlt.rvDecoderFields,
        MulDiv.rvDecoderFields, nz] at fields <;>
      (subst fields; rfl)

/-- A decoder query matching an entry with the row's data fixes the four selector bits, the start PC limbs and the
    three register indices. -/
theorem rv_query_facts {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    {input : RVInput} {entry : RVPooledProgramEntry}
    (data : entry.data = (rvData input).mapFamily (fun _ => .mulDiv))
    (query : (⟨.mulDiv, w⟩ : Row p PooledFamily).decoderQuery = entry.query) :
    (∀ i : Fin 4, w (10 + i.val) = if i = input.operation.selector then 1 else 0) ∧
    (⟨(w 0).val, (w 1).val⟩ : Word) = Word.ofBitVec entry.pc ∧
    w 5 = (input.rs1.toNat : ZMod p) ∧ w 6 = (input.rs2.toNat : ZMod p) ∧
    w 7 = (input.rd.toNat : ZMod p) := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨⟨pc, bits, entryData⟩⟩ := (⟨entry⟩ : Nonempty RVPooledProgramEntry)
  have q (k : Fin 9) := congrArg (fun v : Vector (ZMod p) 9 => v[k]) query
  have q0 := q 0
  have q1 := q 1
  have q2 := q 2
  have q3 := q 3
  have q4 := q 4
  have q8 := q 8
  change w 0 = ((Word.ofBitVec entry.pc).lo : ZMod p) at q0
  change w 1 = ((Word.ofBitVec entry.pc).hi : ZMod p) at q1
  change w 5 = (entry.data.rs1.toNat : ZMod p) at q2
  change w 6 = (entry.data.rs2.toNat : ZMod p) at q3
  change w 7 = (entry.data.rd.toNat : ZMod p) at q4
  change (∑ i : Fin 4, (2 ^ i.val : Nat) * w #[10, 11, 12, 13][i]) = (entry.data.mask : ZMod p) at q8
  rw [data] at q2 q3 q4 q8
  refine ⟨?_, ?_, q2, q3, q4⟩
  · have boolean : ∀ i : Fin 4, w #[10, 11, 12, 13][i] = 0 ∨ w #[10, 11, 12, 13][i] = 1 := by
      intro i
      have bit := (local_flags h).2 i
      fin_cases i <;> simpa using bit
    have small : (rvData input).mask < 512 := by
      cases hop : input.operation <;> simp [rvData, hop, Operation.selector]
    have bits := Trace.Proofs.unpack_decoder_bits_of_width (by omega) (by decide) small boolean q8
    intro i
    have bit := bits i
    cases hop : input.operation <;> fin_cases i <;>
      simpa [rvData, hop, Operation.selector, Nat.testBit, Nat.shiftRight_eq_div_pow] using bit
  · have bound := Word.ofBitVec_bound entry.pc
    rw [q0, q1, ZMod.val_natCast_of_lt (lt_trans bound.1 limbSize),
      ZMod.val_natCast_of_lt (lt_trans bound.2 limbSize)]

end Airbender.MulDiv.Proofs

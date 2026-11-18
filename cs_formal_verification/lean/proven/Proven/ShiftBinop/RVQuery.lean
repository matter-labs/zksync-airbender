module
public import Human.Circuits.ShiftBinop.RVModel
public import Proven.Trace.DecoderBits
public import Proven.ShiftBinop.RVDecoder

@[expose] public section

/-! Native decoder metadata of the RV shift/binop row's instruction (`ShiftBinop.rvDecoderFields`), and what a matching
    decoder query fixes in the row: selectors, operation tag, immediate limbs, PC limbs and register indices. No Sail
    term: the projection is a function of `RV.Instr` (twin of `row_decoder_shape` in `Execution.lean`). -/

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace

/-- The native immediate of a row (as `rowImmediate`): zero for register forms and REV8, the low five bits of the
    encoding for immediate shifts, the bytes of the sign-extended immediate for binary immediates. -/
def rvImmediate (operation : Operation) (immediate : Bool) (imm : BitVec 12) : Word :=
  if operation = .rev8 then ⟨0, 0⟩
  else if immediate then
    if operation.isShift then ⟨(imm.extractLsb' 0 5).toNat, 0⟩ else binaryImmediate (imm.signExtend 32)
  else ⟨0, 0⟩

/-- The decoder data of `rvInstruction input` (`ShiftBinop.rvDecoderFields`). Immediate forms and REV8 read x0 as
    their second source. -/
def rvData (input : RVInput) : DecoderData Unit :=
  ⟨(), input.rs1, if input.immediate || input.operation = .rev8 then 0 else input.rs2, input.rd,
    rvImmediate input.operation input.immediate input.encodedImmediate,
    if input.operation.isShift then 1 else 2, input.operation.tag⟩

private theorem shamt_toNat (s : BitVec 5) : (s.zeroExtend 32).toNat = s.toNat := by
  have := s.isLt
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  omega

/-- The family's projection of `rvInstruction input` is `rvData input` (immediate shift amounts are below 32). -/
theorem rv_fields {input : RVInput} {d : DecoderData Unit}
    (fields : rvDecoderFields (rvInstruction input) = some d) : d = rvData input := by
  obtain ⟨operation, immediate, left, right, pc, rs1, rs2, rd, imm, before⟩ := input
  have small : ((imm.extractLsb' 0 5).zeroExtend 32).toNat < 32 := by
    rw [shamt_toNat]; exact (imm.extractLsb' 0 5).isLt
  cases operation <;> cases immediate <;>
    simp only [rvInstruction, rvDecoderFields, instructionFields, small, ite_true] at fields <;>
    (split at fields
     · cases fields
     · obtain rfl := Option.some.inj fields
       simp [rvData, rvImmediate, Operation.isShift, Operation.tag]
       try omega)

/-- A decoder query matching an entry with the row's data fixes the two selector bits, the operation tag, the
    immediate columns, the start PC limbs and the three register indices. -/
theorem rv_query_facts {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    {input : RVInput} {entry : RVPooledProgramEntry}
    (data : entry.data = (rvData input).mapFamily (fun _ => .shiftBinop))
    (query : (⟨.shiftBinop, w⟩ : Row p PooledFamily).decoderQuery = entry.query) :
    (if input.operation.isShift then w 11 = 1 ∧ w 12 = 0 else w 11 = 0 ∧ w 12 = 1) ∧
    w 10 = (input.operation.tag : ZMod p) ∧
    w 8 = ((rvImmediate input.operation input.immediate input.encodedImmediate).lo : ZMod p) ∧
    w 9 = ((rvImmediate input.operation input.immediate input.encodedImmediate).hi : ZMod p) ∧
    (⟨(w 0).val, (w 1).val⟩ : Word) = Word.ofBitVec entry.pc ∧
    w 5 = (input.rs1.toNat : ZMod p) ∧
    w 6 = ((if input.immediate || input.operation = .rev8 then 0 else input.rs2).toNat : ZMod p) ∧
    w 7 = (input.rd.toNat : ZMod p) := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have q (k : Fin 9) := congrArg (fun v : Vector (ZMod p) 9 => v[k]) query
  have q0 := q 0
  have q1 := q 1
  have q2 := q 2
  have q3 := q 3
  have q4 := q 4
  have q5 := q 5
  have q6 := q 6
  have q7 := q 7
  have q8 := q 8
  change w 0 = ((Word.ofBitVec entry.pc).lo : ZMod p) at q0
  change w 1 = ((Word.ofBitVec entry.pc).hi : ZMod p) at q1
  change w 5 = (entry.data.rs1.toNat : ZMod p) at q2
  change w 6 = (entry.data.rs2.toNat : ZMod p) at q3
  change w 7 = (entry.data.rd.toNat : ZMod p) at q4
  change w 8 = (entry.data.immediate.lo : ZMod p) at q5
  change w 9 = (entry.data.immediate.hi : ZMod p) at q6
  change w 10 = (entry.data.funct3 : ZMod p) at q7
  change (∑ i : Fin 2, (2 ^ i.val : Nat) * w #[11, 12][i]) = (entry.data.mask : ZMod p) at q8
  rw [data] at q2 q3 q4 q5 q6 q7 q8
  refine ⟨?_, q7, q5, q6, ?_, q2, q3, q4⟩
  · have boolean : ∀ i : Fin 2, w #[11, 12][i] = 0 ∨ w #[11, 12][i] = 1 := by
      intro i
      have bit := (local_flags h).2 i
      fin_cases i <;> simpa using bit
    have small : ((rvData input).mapFamily (fun _ => PooledFamily.shiftBinop)).mask < 512 := by
      change (rvData input).mask < 512
      simp only [rvData]
      split <;> decide
    have bits := Trace.Proofs.unpack_decoder_bits_of_width (by omega) (by decide) small boolean q8
    have b0 : w 11 = if (rvData input).mask.testBit 0 then 1 else 0 := bits 0
    have b1 : w 12 = if (rvData input).mask.testBit 1 then 1 else 0 := bits 1
    cases hs : input.operation.isShift <;> simp only [rvData, hs] at b0 b1 ⊢ <;>
      exact ⟨by simpa [Nat.testBit, Nat.shiftRight_eq_div_pow] using b0,
        by simpa [Nat.testBit, Nat.shiftRight_eq_div_pow] using b1⟩
  · have bound := Word.ofBitVec_bound entry.pc
    rw [q0, q1, ZMod.val_natCast_of_lt (lt_trans bound.1 limbSize),
      ZMod.val_natCast_of_lt (lt_trans bound.2 limbSize)]

end Airbender.ShiftBinop.Proofs

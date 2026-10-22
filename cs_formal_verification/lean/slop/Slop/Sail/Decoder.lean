import Slop.Sail.MisaWalk
import Slop.Arithmetic.Word

namespace Airbender.Reference.Sail
open Reference.RiscV.Sail _root_.Sail.ArchSem

/-- The offsets of JAL and branches are even: their implicit zero bit is part of the value. -/
def evenOffsets : SailRV32.instruction → Prop
  | .JAL (imm, _) => imm.toNat % 2 = 0
  | .BTYPE (imm, _, _, _) => imm.toNat % 2 = 0
  | _ => True

private theorem appended_zero_even {n : Nat} (upperBits : BitVec n) :
    (upperBits +++ (0 : BitVec 1)).toNat % 2 = 0 := by
  change (upperBits.toNat <<< 1 ||| 0) % 2 = 0
  simp [Nat.shiftLeft_eq]

open Lean Meta in
/-- The leaf rule of `Walk.prove` in `returns` mode: a `pure` value of the decoder satisfies
    `Q` when it is an instruction whose offset ends in the appended `+++ 0#1` (the JAL and
    branch clauses), or when it has no offset. -/
partial def offsetProof (Q v : Expr) : MetaM Expr := do
  if Q.isAppOfArity ``optionProperty 2 then
    let v ← whnfCore v
    if v.isAppOfArity ``Option.none 1 then return mkConst ``True.intro
    if v.isAppOfArity ``Option.some 2 then return ← offsetProof Q.appArg! v.appArg!
    throwError "offset walk: option value {v} is not a constructor"
  unless Q.isConstOf ``evenOffsets do
    throwError "offset walk: unexpected property {Q}"
  let v ← whnfCore v
  if v.isFVar then throwError "offset walk: value {v} has no property in scope"
  let fn := v.getAppFn
  if fn.isConstOf ``SailRV32.instruction.JAL || fn.isConstOf ``SailRV32.instruction.BTYPE then
    -- JAL (imm, rd) and BTYPE (imm, …): the offset is the first component of the tuple
    let tuple ← whnfCore v.appArg!
    let imm ← whnfCore (tuple.getArg! 2)
    unless imm.getAppNumArgs ≥ 2 do
      throwError "offset walk: offset {imm} is not an appended value"
    let upper := imm.getArg! (imm.getAppNumArgs - 2)
    let n := (← inferType upper).appArg!
    return mkApp2 (mkConst ``appended_zero_even) n upper
  return mkConst ``True.intro

open Lean Elab Tactic in
/-- Closes `Returns evenOffsets e` for the goal's decoder body `e` (unfold the decoder first). -/
elab "offset_walk" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  let pf ← Walk.prove { mode := .returns offsetProof, leaves := fun _ _ => pure none }
    (ty.getArg! 0) (ty.getArg! 1) ty.appArg!
  g.assign pf
  replaceMainGoal []

set_option maxRecDepth 65536 in
/-- The original decoder supplies the implicit zero bit of JAL/branch offsets.
    This holds for successful decoding, including any effects in other clauses. -/
theorem decoded_offset_even (bits : BitVec 32) :
    ∀ before instruction after,
      run (SailRV32.Functions.encdec_backwards bits) before = .ok instruction after →
      match instruction with
      | .JAL (imm, _) => imm.toNat % 2 = 0
      | .BTYPE (imm, _, _, _) => imm.toNat % 2 = 0
      | _ => True := by
  have checked : Returns evenOffsets (SailRV32.Functions.encdec_backwards bits) := by
    unfold SailRV32.Functions.encdec_backwards
    offset_walk
  unfold Returns at checked
  exact checked

/-- Word encoding and sign extension preserve the decoded offset's zero bit. -/
theorem sign_extend_low_even {n : Nat} (positive : 0 < n) (bits : BitVec n)
    (even : bits.toNat % 2 = 0) :
    (Arithmetic.Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) bits)).lo % 2 = 0 := by
  have low : bits.getLsbD 0 = false := Nat.mod_two_eq_zero_iff_testBit_zero.mp even
  have extended : (bits.signExtend 32).getLsbD 0 = false := by
    rw [BitVec.getLsbD_signExtend, ite_eq_left positive, low, Bool.and_false]
  have evenExtended : (bits.signExtend 32).toNat % 2 = 0 :=
    Nat.mod_two_eq_zero_iff_testBit_zero.mpr extended
  change ((bits.signExtend 32).toNat % 65536) % 2 = 0
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 65536)]
  exact evenExtended

end Airbender.Reference.Sail

import Slop.Equiv.Walk
import Mathlib.Tactic.IntervalCases

/-! Closing a decoder row after `walk_decoder`: Sail's decoded instruction (fields as bit slices of the word)
equals `toSail` of our decoded instruction (fields as decoded values), field by field, bit by bit. -/

open Sail SailRV32 SailRV32.Functions

open Lean Meta Elab Tactic in
/-- Put the known bits (`Bits` hypotheses) into the goal: every fully known slice becomes a literal. -/
elab "subst_known" : tactic => withMainContext do
  let facts ← Slop.Equiv.getFacts
  let g ← getMainGoal
  let (e, pf) ← Slop.Equiv.substKnown facts (← g.getType)
  let some pf := pf | return
  replaceMainGoal [← g.replaceTargetEq e pf]

open Lean Meta Elab Tactic in
/-- Each `Bits` hypothesis, also as single-bit facts `w.getLsbD i = …`. -/
elab "bits_lsb" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).isAppOfArity ``Slop.Equiv.Bits 4 then
      let pf ← mkAppM ``Slop.Equiv.getLsbD_of_bits #[d.toExpr]
      let (_, g') ← (← g.assert (← mkFreshUserName `hbit) (← inferType pf) pf).intro1P
      g := g'
  replaceMainGoal [g]

/-- One field: Sail's bit slices = our decoded value, compared bit by bit. -/
macro "close_field" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  try simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.regidx_bit_width] at hj ⊢
  try simp only [Nat.reduceAdd, Nat.reduceSub] at hj
  have hj32 : j < 32 := by omega
  first
    | (simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
        BitVec.getElem_signExtend, BitVec.getElem_append, BitVec.getLsbD_setWidth, BitVec.getElem_setWidth, hj, hj32]
       done)
    | (simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_signExtend, BitVec.getElem_signExtend,
         BitVec.getLsbD_setWidth, BitVec.getElem_setWidth, hj, hj32]
       rw [BitVec.getLsbD_append]
       simp [BitVec.getLsbD_extractLsb', hj, hj32]
       all_goals omega)
    | (interval_cases j <;> (simp_all [BitVec.getLsbD_extractLsb', BitVec.getLsbD_signExtend,
         BitVec.getElem_signExtend, BitVec.getLsbD_setWidth, BitVec.getElem_setWidth, BitVec.getLsbD_append,
         BitVec.getElem_append]; done))))

/-- After `walk_decoder`: the goal `runF (pure x) σ = .ok (toSail i) σ`, closed field by field. -/
macro "close_row" : tactic => `(tactic| (
  rw [Slop.runF_pure]
  subst_known
  bits_lsb
  simp only [Airbender.toSail, Airbender.sailBop, Airbender.sailRop, EStateM.Result.ok.injEq,
    instruction.UTYPE.injEq, instruction.JAL.injEq, instruction.JALR.injEq, instruction.BTYPE.injEq,
    instruction.ITYPE.injEq, instruction.SHIFTIOP.injEq, instruction.RTYPE.injEq, instruction.LOAD.injEq,
    instruction.STORE.injEq, instruction.MUL.injEq, instruction.DIV.injEq, instruction.REM.injEq,
    Prod.mk.injEq, and_true, true_and]
  and_intros
  all_goals first | rfl | decide | (congr 1; close_field) | close_field))

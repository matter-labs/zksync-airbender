import Airbender.Proofs.FullUnsigned.SourceIndexWords

namespace Airbender.Setup.SourceIndices
set_option warningAsError true
set_option Elab.async false

theorem decode_take (base first rest packed : Nat) :
    (decode base (first + rest) packed).take first = decode base first packed := by
  induction first generalizing packed with
  | zero => rfl
  | succ first ih =>
    rw [Nat.succ_add, decode_succ, List.take_succ_cons, ih, decode_succ]

theorem decode_mod (base count packed : Nat) :
    decode base count packed = decode base count (packed % base ^ count) := by
  induction count generalizing packed with
  | zero => rfl
  | succ count ih =>
    rw [decode_succ, decode_succ, Nat.pow_succ, Nat.mod_mul_left_mod,
      Nat.mod_mul_left_div_self, ← ih]

/-- An exact digit window follows from its original scalar encoding. -/
theorem slice_from_word {entries digits : List Nat}
    {base total first count rest packed fp cp word : Nat}
    (encoded : entries = decode base total packed)
    (part : Encoded base digits count word) (positive : 0 < base)
    (totalEq : total = first + (count + rest))
    (firstPower : Nat.pow base first = fp) (countPower : Nat.pow base count = cp)
    (wordEq : (packed / fp) % cp = word) :
    (entries.drop first).take count = digits := by
  simp only [Nat.pow_eq] at firstPower countPower
  rw [encoded, totalEq, decode_drop, decode_take, decode_mod, firstPower, countPower, wordEq]
  exact part.decode positive

open Lean Meta Elab Tactic

/-- Supply explicit scalar arguments to the proved slice rule. The kernel
checks the source encoding, the bounded digits and both power certificates. -/
elab "index_word_slice " source:ident part:ident " slice_start " first:num
    " slice_power_proofs " fp:ident cp:ident " slice_word_proof " word:ident : tactic => do
  let encoded := mkConst (← resolveGlobalConstNoOverload source)
  let ep := (← inferType encoded).getAppArgs
  let data := ep[1]!
  let decoded := ep[2]!.getAppArgs
  let base ← getNatValue? decoded[0]!
  let total ← getNatValue? decoded[1]!
  let some base := base | throwError "expected a scalar source radix"
  let some total := total | throwError "expected a scalar source length"
  let retained := mkConst (← resolveGlobalConstNoOverload part)
  let rp := (← inferType retained).getAppArgs
  let some count ← getNatValue? rp[2]! | throwError "expected a scalar slice length"
  unless first.getNat + count ≤ total do throwError "source slice exceeds its encoded length"
  let fpp := mkConst (← resolveGlobalConstNoOverload fp)
  let cpp := mkConst (← resolveGlobalConstNoOverload cp)
  let wp := mkConst (← resolveGlobalConstNoOverload word)
  let fpv := (← inferType fpp).getAppArgs[2]!
  let cpv := (← inferType cpp).getAppArgs[2]!
  let positive ← mkDecideProof (← mkAppM ``LT.lt #[mkRawNatLit 0, mkRawNatLit base])
  let totalEq ← mkEqRefl (mkRawNatLit total)
  let proof := mkAppN (mkConst ``slice_from_word) #[data, rp[1]!, mkRawNatLit base,
    mkRawNatLit total, mkRawNatLit first.getNat, mkRawNatLit count,
    mkRawNatLit (total - first.getNat - count), decoded[2]!, fpv, cpv, rp[3]!,
    encoded, retained, positive, totalEq, fpp, cpp, wp]
  let goal ← getMainGoal
  goal.assign proof
  replaceMainGoal []

end Airbender.Setup.SourceIndices

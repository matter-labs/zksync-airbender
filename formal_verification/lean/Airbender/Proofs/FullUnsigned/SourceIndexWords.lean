import Airbender.Proofs.FullUnsigned.SetupSourceIndices
import Mathlib.Data.Nat.Digits.Defs

namespace Airbender.Setup.SourceIndices
set_option warningAsError true
set_option Elab.async false

/-- A fixed number of bounded digits has its exact little-endian encoding. -/
theorem decode_ofDigits (base : Nat) (digits : List Nat) (positive : 0 < base)
    (bounded : ∀ digit ∈ digits, digit < base) :
    decode base digits.length (Nat.ofDigits base digits) = digits := by
  induction digits with
  | nil => rfl
  | cons head rest ih =>
    have headBound : head < base := bounded head (by simp)
    have tailBound : ∀ digit ∈ rest, digit < base := fun digit member => bounded digit (by simp [member])
    rw [List.length_cons, decode_succ, Nat.ofDigits_cons]
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt headBound,
      Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt headBound, Nat.zero_add]
    rw [ih tailBound]

/-- A repeated index group ends at the supplied suffix word. -/
def repeatWordTail (step word tail : Nat) : Nat → Nat
  | 0 => tail
  | count + 1 => word + step * repeatWordTail step word tail count

theorem ofDigits_repeat_suffix (base count : Nat) (digits tail : List Nat) :
    Nat.ofDigits base (((List.replicate count digits).flatten) ++ tail) =
      repeatWordTail (base ^ digits.length) (Nat.ofDigits base digits) (Nat.ofDigits base tail) count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.append_assoc,
      Nat.ofDigits_append (l1 := digits), repeatWordTail, ih]

/-- Keep the scalar word separate from the represented list during conversion. -/
def Encoded (base : Nat) (digits : List Nat) (length word : Nat) : Prop :=
  digits.length = length ∧ (∀ digit ∈ digits, digit < base) ∧ Nat.ofDigits base digits = word

/-- Check a short prefix, a repeated group, and a short suffix through their
scalar words. The list itself does not need normalization. -/
theorem Encoded.grammar {base : Nat} {front cycle tail : List Nat}
    {fl cl tl fw cw tw fp cp result : Nat}
    (a : Encoded base front fl fw) (b : Encoded base cycle cl cw)
    (c : Encoded base tail tl tw) (count : Nat)
    (frontPower : Nat.pow base fl = fp) (cyclePower : Nat.pow base cl = cp)
    (wordEq : fw + fp * repeatWordTail cp cw tw count = result) :
    Encoded base (front ++ (List.replicate count cycle).flatten ++ tail)
      (fl + count * cl + tl) result := by
  have sumCopies : (List.replicate count cl).sum = count * cl := by
    clear wordEq
    induction count with
    | zero => simp only [List.replicate_zero, List.sum_nil, Nat.zero_mul]
    | succ count ih => simp only [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]
  simp only [Nat.pow_eq] at frontPower cyclePower
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_flatten, List.map_replicate,
      a.1, b.1, c.1, sumCopies]
  · intro digit member
    rcases List.mem_append.mp member with earlier | last
    · rcases List.mem_append.mp earlier with first | repeated
      · exact a.2.1 digit first
      · obtain ⟨copy, copied, present⟩ := List.mem_flatten.mp repeated
        have same : copy = cycle := (List.mem_replicate.mp copied).2
        exact b.2.1 digit (same ▸ present)
    · exact c.2.1 digit last
  · rw [List.append_assoc, Nat.ofDigits_append (l1 := front), ofDigits_repeat_suffix,
      a.2.2, b.2.2, c.2.2, a.1, b.1, frontPower, cyclePower, wordEq]

theorem Encoded.decode {base : Nat} {digits : List Nat} {length word : Nat}
    (part : Encoded base digits length word) (positive : 0 < base) :
    decode base length word = digits := by
  rw [← part.1, ← part.2.2]
  exact decode_ofDigits base digits positive part.2.1

open Lean Meta Elab Command

private theorem power_zero (base : Nat) : Nat.pow base 0 = 1 := rfl

private theorem power_even (base total half value result : Nat)
    (totalEq : total = half + half) (previous : Nat.pow base half = value)
    (product : value * value = result) : Nat.pow base total = result := by
  simp only [Nat.pow_eq] at previous ⊢
  rw [totalEq, Nat.pow_add, previous, product]

private theorem power_odd (base total half value result : Nat)
    (totalEq : total = half + half + 1) (previous : Nat.pow base half = value)
    (product : value * value * base = result) : Nat.pow base total = result := by
  simp only [Nat.pow_eq] at previous ⊢
  rw [totalEq, Nat.pow_succ, Nat.pow_add, previous, product]

private partial def binaryPower (base count : Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  if count = 0 then return (mkRawNatLit 1, mkApp (mkConst ``power_zero) (mkRawNatLit base))
  let (value, previous) ← binaryPower base (count / 2)
  let number := value.rawNatLit?.getD 0
  let same ← mkEqRefl (mkRawNatLit count)
  let square := mkApp2 (mkConst ``Nat.mul) value value
  if count % 2 = 0 then
    let proof ← mkEqRefl square
    let result := mkRawNatLit (number * number)
    return (result, mkAppN (mkConst ``power_even) #[mkRawNatLit base, mkRawNatLit count,
      mkRawNatLit (count / 2), value, result, same, previous, proof])
  else
    let proof ← mkEqRefl (mkApp2 (mkConst ``Nat.mul) square (mkRawNatLit base))
    let result := mkRawNatLit (number * number * base)
    return (result, mkAppN (mkConst ``power_odd) #[mkRawNatLit base, mkRawNatLit count,
      mkRawNatLit (count / 2), value, result, same, previous, proof])

/-- Propose a logarithmic arithmetic proof. The kernel checks each product. -/
elab "certify_index_power " name:ident " radix_value " base:num " power_count " count:num : command => do
  let fullName := (← getCurrNamespace) ++ name.getId
  let (value, proof) ← liftTermElabM <| binaryPower base.getNat count.getNat
  let type ← liftTermElabM <| mkEq
    (mkApp2 (mkConst ``Nat.pow) (mkRawNatLit base.getNat) (mkRawNatLit count.getNat)) value
  liftCoreM <| addDecl (.thmDecl { name := fullName, levelParams := [], type := type, value := proof })

/-- Build the ordinary grammar theorem with explicit scalar arguments. This
avoids normalization of powers while the elaborator infers arguments. -/
elab "index_word_grammar " front:ident cycle:ident tail:ident " repeat_count " count:num
    " power_proofs " fp:ident cp:ident " word_proof " word:ident : tactic => do
  let a := mkConst (← resolveGlobalConstNoOverload front)
  let b := mkConst (← resolveGlobalConstNoOverload cycle)
  let c := mkConst (← resolveGlobalConstNoOverload tail)
  let af := (← inferType a).getAppArgs
  let bf := (← inferType b).getAppArgs
  let cf := (← inferType c).getAppArgs
  let fpp := mkConst (← resolveGlobalConstNoOverload fp)
  let cpp := mkConst (← resolveGlobalConstNoOverload cp)
  let wp := mkConst (← resolveGlobalConstNoOverload word)
  let fpv := (← inferType fpp).getAppArgs[2]!
  let cpv := (← inferType cpp).getAppArgs[2]!
  let result := (← inferType wp).getAppArgs[2]!
  let proof := mkAppN (mkConst ``Encoded.grammar) #[af[0]!, af[1]!, bf[1]!, cf[1]!,
    af[2]!, bf[2]!, cf[2]!, af[3]!, bf[3]!, cf[3]!, fpv, cpv, result,
    a, b, c, mkRawNatLit count.getNat, fpp, cpp, wp]
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.assign proof
  Lean.Elab.Tactic.replaceMainGoal []

end Airbender.Setup.SourceIndices

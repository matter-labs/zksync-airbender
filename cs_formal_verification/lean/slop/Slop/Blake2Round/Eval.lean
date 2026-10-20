import Slop.OpIndex
import Human.Helpers.Properties

/-!
Evaluation of one entry of a row after `interval_cases j`, for the lookup-padding proofs
(lean-strategies §2.1, §2.4). `eval_entry [extra, …]` is `simp only` with the shared set plus `extra`.

The pre-rewrite `↓Vector.getElem_map` selects entry `j` before the rest of the row is evaluated.
Without it every `simp` call evaluates all entries of the row (ColumnGQueries0: 156 calls, 33 s of
simp; with it, about 10 s).
-/

open Lean

syntax "eval_entry" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| eval_entry) => `(tactic| simp only [↓Vector.getElem_map,
      Airbender.Verification.environment, Fin.isValue, Int.ofNat_eq_natCast, CharP.cast_eq_zero,
      Int.cast_zero, Nat.cast_one, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Nat.cast_ofNat,
      Int.reduceNegSucc, Fin.getElem_fin, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      Expression.eval, add_zero, mul_one, mul_zero, one_mul, zero_add, mul_neg, neg_mul,
      Nat.reduceAdd, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ])
  | `(tactic| eval_entry [ $xs,* ]) => `(tactic| simp only [↓Vector.getElem_map,
      Airbender.Verification.environment, Fin.isValue, Int.ofNat_eq_natCast, CharP.cast_eq_zero,
      Int.cast_zero, Nat.cast_one, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Nat.cast_ofNat,
      Int.reduceNegSucc, Fin.getElem_fin, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      Expression.eval, add_zero, mul_one, mul_zero, one_mul, zero_add, mul_neg, neg_mul,
      Nat.reduceAdd, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, $xs,*])

module
import all Mathlib.Data.List.Sort
public import Mathlib.Data.List.Sort
public import Proven.GKRCompiler.Certificate
public import Mathlib.Data.ZMod.Basic

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.NumericPolynomialChecks

abbrev Data := List (Nat × List Nat)

def encode (polynomial : Polynomial n (ZMod p)) : Data :=
  polynomial.map fun term => (term.1.val, term.2.map Fin.val)

def monomialCompare (left : List Nat) (right : List Nat) : Ordering :=
  match left with
  | [] => match right with | [] => .eq | _ :: _ => .lt
  | first :: rest => match right with
    | [] => .gt
    | second :: tail => match compare first second with
      | .eq => monomialCompare rest tail
      | result => result
termination_by structural left

def insertTerm (p : Nat) (term : Nat × List Nat) : Data → Data
  | [] => if term.1 == 0 then [] else [term]
  | head :: tail =>
      if term.1 == 0 then head :: tail
      else if term.2 == head.2 then
        let sum := (term.1 + head.1) % p
        if sum == 0 then tail else (sum, term.2) :: tail
      else if monomialCompare term.2 head.2 == .lt then term :: head :: tail
      else head :: insertTerm p term tail

def normalize (p : Nat) (polynomial : Data) : Data :=
  polynomial.foldr (fun term result => insertTerm p
    (term.1, term.2.insertionSort (fun a b => a ≤ b)) result) []

def equal (p : Nat) (left right : Data) : Bool := normalize p left == normalize p right

def multiply (p : Nat) (left right : Data) : Data :=
  left.flatMap fun a => right.map fun b => ((a.1 * b.1) % p, a.2 ++ b.2)

def rename (placement : Nat → Nat) (polynomial : Data) : Data :=
  polynomial.map fun term => (term.1, term.2.map placement)

def substitute (p : Nat) (extension : Nat → Data) (polynomial : Data) : Data :=
  polynomial.flatMap fun term => multiply p [(term.1, [])]
    (term.2.foldr (fun wire result => multiply p (extension wire) result) [(1 % p, [])])

def combination (p : Nat) (relations : List Data) (terms : List (Data × Nat)) : Data :=
  terms.foldr (fun term result => multiply p term.1 ((relations[term.2]?).getD []) ++ result) []

theorem monomial_injective : Function.Injective (List.map (Fin.val : Fin n → Nat)) :=
  List.map_injective_iff.mpr Fin.val_injective

theorem encode_injective [NeZero p] : Function.Injective (@encode n p) := by
  apply List.map_injective_iff.mpr
  intro a b same
  apply Prod.ext
  · exact ZMod.val_injective p (congrArg Prod.fst same)
  · exact monomial_injective (congrArg (fun term : Nat × List Nat => term.2) same)

theorem compare_encode (left right : Monomial n) :
    monomialCompare (left.map Fin.val) (right.map Fin.val) = compare left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons first rest ih =>
      cases right with
      | nil => rfl
      | cons second tail =>
          simp only [List.map_cons, monomialCompare, List.compare_eq_compareLex, List.compareLex]
          change (match compare first.val second.val with
            | .eq => monomialCompare (rest.map Fin.val) (tail.map Fin.val)
            | result => result) =
            (match compare first.val second.val with
            | .lt => .lt
            | .eq => List.compareLex compare rest tail
            | .gt => .gt)
          cases compare first.val second.val <;> simp only [ih, List.compare_eq_compareLex]

theorem encode_insertTerm [NeZero p] (term : ZMod p × Monomial n)
    (polynomial : Polynomial n (ZMod p)) :
    encode (Airbender.Compiler.insertTerm term polynomial) =
      insertTerm p (term.1.val, term.2.map Fin.val) (encode polynomial) := by
  induction polynomial with
  | nil => simp only [Airbender.Compiler.insertTerm, insertTerm, encode, List.map_nil,
      beq_iff_eq, ZMod.val_eq_zero]; split_ifs <;> rfl
  | cons head tail ih =>
      simp only [Airbender.Compiler.insertTerm, insertTerm, encode, List.map_cons,
        beq_iff_eq, ZMod.val_eq_zero, ← ZMod.val_add, monomial_injective.eq_iff, compare_encode]
      split_ifs <;> simp_all only [encode, List.map_cons]

theorem encode_normalize [NeZero p] (polynomial : Polynomial n (ZMod p)) :
    encode (Airbender.Compiler.normalize polynomial) = normalize p (encode polynomial) := by
  induction polynomial with
  | nil => rfl
  | cons head tail ih =>
      change encode (Airbender.Compiler.insertTerm
        (head.1, head.2.insertionSort (fun a b => a.val ≤ b.val))
        (Airbender.Compiler.normalize tail)) =
        insertTerm p (head.1.val, (head.2.map Fin.val).insertionSort (fun a b => a ≤ b))
          (normalize p (encode tail))
      rw [encode_insertTerm, ih]
      rw [List.map_insertionSort (fun a b : Fin n => a.val ≤ b.val)
        (fun a b : Nat => a ≤ b) Fin.val head.2 (by intros; rfl)]

theorem equal_encode [NeZero p] (left right : Polynomial n (ZMod p)) :
    equal p (encode left) (encode right) = Airbender.Compiler.equal left right := by
  apply Bool.eq_iff_iff.mpr
  simp only [equal, Airbender.Compiler.equal, ← encode_normalize, beq_iff_eq,
    decide_eq_true_eq, encode_injective.eq_iff]

theorem encode_append (left right : Polynomial n (ZMod p)) :
    encode (left ++ right) = encode left ++ encode right := List.map_append ..

theorem encode_atom (wire : Fin n) : encode (Airbender.Compiler.atom (F := ZMod p) wire) = [(1 % p, [wire.val])] := by
  simp only [encode, Airbender.Compiler.atom, List.map_cons, List.map_nil, ZMod.val_one_eq_one_mod]

theorem encode_multiply (left right : Polynomial n (ZMod p)) :
    encode (Airbender.Compiler.multiply left right) = multiply p (encode left) (encode right) := by
  simp only [encode, Airbender.Compiler.multiply, multiply, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def, ZMod.val_mul, List.map_append]

theorem encode_rename (placement : Fin n → Fin m) (numericPlacement : Nat → Nat)
    (compatible : ∀ wire, numericPlacement wire.val = (placement wire).val)
    (polynomial : Polynomial n (ZMod p)) :
    encode (Airbender.Compiler.rename placement polynomial) = rename numericPlacement (encode polynomial) := by
  have same : (fun wire => (placement wire).val) = (fun wire => numericPlacement wire.val) :=
    funext fun wire => (compatible wire).symm
  simp only [encode, Airbender.Compiler.rename, rename, List.map_map, Function.comp_def]
  rw [same]

theorem encode_substitute (extension : Fin m → Polynomial n (ZMod p)) (numericExtension : Nat → Data)
    (compatible : ∀ wire, numericExtension wire.val = encode (extension wire))
    (polynomial : Polynomial m (ZMod p)) :
    encode (Airbender.Compiler.substitute extension polynomial) =
      substitute p numericExtension (encode polynomial) := by
  have product (monomial : Monomial m) :
      encode (monomial.foldr (fun wire result => Airbender.Compiler.multiply (extension wire) result)
        (constant 1)) =
      (monomial.map Fin.val).foldr (fun wire result => multiply p (numericExtension wire) result) [(1 % p, [])] := by
    induction monomial with
    | nil => simp only [List.foldr_nil, encode, constant, List.map_cons, List.map_nil, ZMod.val_one_eq_one_mod]
    | cons wire tail ih =>
        simp only [List.foldr_cons, List.map_cons]
        rw [encode_multiply, ← compatible wire, ih]
  simp only [Airbender.Compiler.substitute, substitute, encode, List.map_flatMap, List.flatMap_map]
  congr 1
  funext term
  change encode (Airbender.Compiler.multiply (constant term.1)
    (term.2.foldr (fun wire result => Airbender.Compiler.multiply (extension wire) result) (constant 1))) = _
  rw [encode_multiply, product]
  rfl

def encodeCombination (terms : List (Polynomial n (ZMod p) × Fin bound)) : List (Data × Nat) :=
  terms.map fun term => (encode term.1, term.2.val)

theorem encode_combination (relations : List (Polynomial n (ZMod p))) (terms : Combination relations) :
    encode (Airbender.Compiler.combination relations terms) =
      combination p (relations.map encode) (encodeCombination terms) := by
  have get (index : Fin relations.length) :
      ((relations.map encode)[index.val]?).getD [] = encode (relations.get index) := by
    simp only [List.getElem?_map, List.getElem?_eq_getElem index.isLt, Option.map_some,
      Option.getD_some, List.get_eq_getElem]
  induction terms with
  | nil => rfl
  | cons term tail ih =>
      change encode (Airbender.Compiler.multiply term.1 (relations.get term.2) ++
        Airbender.Compiler.combination relations tail) =
        multiply p (encode term.1) (((relations.map encode)[term.2.val]?).getD []) ++
          combination p (relations.map encode) (encodeCombination tail)
      rw [encode_append, encode_multiply, ih, get]

end Airbender.Compiler.NumericPolynomialChecks

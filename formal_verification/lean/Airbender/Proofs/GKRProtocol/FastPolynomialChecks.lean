import Airbender.Proofs.GKRCompiler.Polynomial

namespace Airbender.Compiler.FastPolynomialChecks
set_option warningAsError true

def insertTerm {n : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F]
    (term : F × Monomial n) : Polynomial n F → Polynomial n F
  | [] => if term.1 == 0 then [] else [term]
  | head :: tail =>
      if term.1 == 0 then head :: tail
      else if term.2 == head.2 then
        if term.1 + head.1 == 0 then tail else (term.1 + head.1, term.2) :: tail
      else if compare term.2 head.2 == .lt then term :: head :: tail
      else head :: insertTerm term tail

theorem insertTerm_eq {n : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (term : F × Monomial n) (polynomial : Polynomial n F) :
    insertTerm term polynomial = Airbender.Compiler.insertTerm term polynomial := by
  induction polynomial with
  | nil => simp only [insertTerm, Airbender.Compiler.insertTerm, beq_iff_eq]
  | cons head tail ih => simp only [insertTerm, Airbender.Compiler.insertTerm, beq_iff_eq, ih]

def normalize {n : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F]
    (polynomial : Polynomial n F) : Polynomial n F :=
  polynomial.foldr (fun term result =>
    insertTerm (term.1, term.2.insertionSort (fun a b => a.val ≤ b.val)) result) []

theorem normalize_eq {n : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (polynomial : Polynomial n F) : normalize polynomial = Airbender.Compiler.normalize polynomial := by
  simp only [normalize, Airbender.Compiler.normalize, insertTerm_eq]

def equal {n : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F]
    (left right : Polynomial n F) : Bool := normalize left == normalize right

theorem equal_eq {n : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (left right : Polynomial n F) : equal left right = Airbender.Compiler.equal left right := by
  apply Bool.eq_iff_iff.mpr
  simp only [equal, Airbender.Compiler.equal, normalize_eq, beq_iff_eq, decide_eq_true_eq]

end Airbender.Compiler.FastPolynomialChecks

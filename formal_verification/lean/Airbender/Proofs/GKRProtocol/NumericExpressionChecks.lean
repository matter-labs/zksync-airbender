import Airbender.Proofs.GKRProtocol.NumericPolynomialChecks
import Airbender.Proofs.GKRCompiler.Arithmetic

namespace Airbender.Compiler.NumericExpressionChecks
set_option warningAsError true

inductive Code where
  | constant (value : Nat)
  | atom (wire : Nat)
  | add (left right : Code)
  | mul (left right : Code)

def Code.polynomial (p : Nat) : Code → NumericPolynomialChecks.Data
  | .constant value => [(value, [])]
  | .atom wire => [(1 % p, [wire])]
  | .add left right => Code.polynomial p left ++ Code.polynomial p right
  | .mul left right => NumericPolynomialChecks.multiply p (Code.polynomial p left) (Code.polynomial p right)

def encode : Expression n (ZMod p) → Code
  | .constant value => .constant value.val
  | .atom wire => .atom wire.val
  | .add left right => .add (encode left) (encode right)
  | .mul left right => .mul (encode left) (encode right)

/-- Erase coefficients and variables before polynomial expansion. Preserve every term. -/
theorem encode_polynomial (expression : Expression n (ZMod p)) :
    NumericPolynomialChecks.encode expression.polynomial = Code.polynomial p (encode expression) := by
  induction expression with
  | constant value => rfl
  | atom wire => exact NumericPolynomialChecks.encode_atom wire
  | add left right ihLeft ihRight =>
      simp only [Expression.polynomial, encode, Code.polynomial, Compiler.add,
        NumericPolynomialChecks.encode_append, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp only [Expression.polynomial, encode, Code.polynomial,
        NumericPolynomialChecks.encode_multiply, ihLeft, ihRight]

/-- Bind complete expression and helper banks to the original source polynomials. -/
theorem source_binding (expressions : List (Expression n (ZMod p)))
    (helpers : List (Polynomial n (ZMod p))) (codes : List Code)
    (helperRows rows : List NumericPolynomialChecks.Data)
    (expressionsBound : expressions.map encode = codes)
    (helpersBound : helpers.map NumericPolynomialChecks.encode = helperRows)
    (rowsBound : codes.map (Code.polynomial p) ++ helperRows = rows) :
    (expressions.map Expression.polynomial ++ helpers).map NumericPolynomialChecks.encode = rows := by
  have original : expressions.map (fun expression => NumericPolynomialChecks.encode expression.polynomial) =
      codes.map (Code.polynomial p) := by
    rw [← expressionsBound, List.map_map]
    apply List.map_congr_left
    intro expression _
    exact encode_polynomial expression
  calc
    _ = expressions.map (fun expression => NumericPolynomialChecks.encode expression.polynomial) ++ helperRows := by
      rw [List.map_append, helpersBound, List.map_map]
      rfl
    _ = codes.map (Code.polynomial p) ++ helperRows := congrArg (fun items => items ++ helperRows) original
    _ = rows := rowsBound

end Airbender.Compiler.NumericExpressionChecks

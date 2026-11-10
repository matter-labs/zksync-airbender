import Mathlib.Algebra.Ring.Defs

namespace Airbender.Compiler

/-- Typed arithmetic syntax retains the source expression tree. Bounds on
native variable/address indices are checked when constructing each leaf. -/
inductive Expression (arity : Nat) (F : Type) where
  | constant : F → Expression arity F
  | atom : Fin arity → Expression arity F
  | add : Expression arity F → Expression arity F → Expression arity F
  | mul : Expression arity F → Expression arity F → Expression arity F
  deriving Repr, DecidableEq

def Expression.value [CommRing F] (values : Fin n → F) : Expression n F → F
  | .constant value => value
  | .atom wire => values wire
  | .add left right => left.value values + right.value values
  | .mul left right => left.value values * right.value values

/-- Native arithmetic relation forms. Both sparse input and structured
expression fields are retained and their equality is checked independently. -/
inductive ArithmeticGate (arity : Nat) (F : Type) where
  | assertZero (input expression : Expression arity F)
  | define (output : Fin arity) (input expression : Expression arity F)
  | copy (output input : Fin arity)
  deriving Repr, DecidableEq

def ArithmeticGate.expressionResidual [CommRing F] (values : Fin n → F) : ArithmeticGate n F → F
  | .assertZero _ expression => expression.value values
  | .define output _ expression => values output - expression.value values
  | .copy output input => values output - values input

structure ArithmeticArtifact (sourceVariables lowerVariables : Nat) (F : Type) where
  source : List (Expression sourceVariables F)
  gates : List (ArithmeticGate lowerVariables F)
  placement : Fin sourceVariables → Fin lowerVariables

def ArithmeticArtifact.SourceHolds [CommRing F] (artifact : ArithmeticArtifact n m F)
    (values : Fin n → F) : Prop := ∀ expression ∈ artifact.source, expression.value values = 0

def ArithmeticArtifact.LoweredHolds [CommRing F] (artifact : ArithmeticArtifact n m F)
    (values : Fin m → F) : Prop := ∀ gate ∈ artifact.gates, gate.expressionResidual values = 0

inductive Configuration where
  | addSubCached
  | addSubUncached
  | bigintCached
  | bigintUncached
  | blakeGCached
  | blakeGUncached
  | blakeRoundCached
  | blakeRoundUncached
  | jumpBranchCached
  | jumpBranchUncached
  | keccakCached
  | keccakUncached
  | mulDivCached
  | mulDivUncached
  | shiftBinopCached
  | shiftBinopUncached
  | subwordMemoryCached
  | subwordMemoryUncached
  | unifiedCached
  | unifiedUncached
  | wordMemoryCached
  | wordMemoryUncached

structure CapturedArithmetic (F : Type) where
  sourceVariables : Nat
  lowerVariables : Nat
  artifact : ArithmeticArtifact sourceVariables lowerVariables F
  selected : List (Fin artifact.gates.length)

end Airbender.Compiler

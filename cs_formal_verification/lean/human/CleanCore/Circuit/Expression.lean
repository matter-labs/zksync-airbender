module
public import Mathlib.Algebra.Field.Basic
-- Clean's Mathlib/Lean imports for this file, re-exported so importers see what they saw through Clean
public import Lean.Meta.Tactic.Simp.RegisterCommand

/-! # Expressions and environments (Clean `Clean.Circuit.Expression`, pinned b41c196)

The part of Clean's constraint language our circuits use, transcribed: a polynomial expression over
witness variables, evaluated in an environment. Same constructors, fields and definitions as Clean;
`CleanEquivalence` proves the correspondence. Deviation: the prover-only `ProverEnvironment`/`ProverHint`
(completeness witnesses) are omitted. -/

@[expose] public section

namespace Airbender

variable {F : Type}

structure Variable (F : Type) where
  index : ℕ

inductive Expression (F : Type) where
  | var : Variable F → Expression F
  | const : F → Expression F
  | add : Expression F → Expression F → Expression F
  | mul : Expression F → Expression F → Expression F

/-- Data a prover witnesses outside the circuit (e.g. lookup-table contents), by name and arity. -/
def ProverData (F : Type) :=
  String → (n : ℕ) → Array (Vector F n)

/-- A full witness assignment (`get`) plus the external witness data (`data`). -/
structure Environment (F : Type) where
  get : ℕ → F
  data : ProverData F

namespace Expression
variable [Field F]

def eval (env : Environment F) : Expression F → F
  | var v => env.get v.index
  | const c => c
  | add x y => eval env x + eval env y
  | mul x y => eval env x * eval env y

instance : Zero (Expression F) where zero := const 0
instance : One (Expression F) where one := const 1
instance : Add (Expression F) where add := add
instance : Neg (Expression F) where neg e := mul (const (-1)) e
instance : Sub (Expression F) where sub e₁ e₂ := add e₁ (-e₂)
instance : Mul (Expression F) where mul := mul
instance : Coe F (Expression F) where coe f := const f
instance {n : ℕ} [OfNat F n] : OfNat (Expression F) n where
  ofNat := const (OfNat.ofNat n)
instance : HMul F (Expression F) (Expression F) where hMul f e := mul f e
instance : HMul (Expression F) F (Expression F) where hMul f e := mul f e

end Expression

instance [Field F] : CoeFun (Environment F) (fun _ => (Expression F) → F) where
  coe env x := x.eval env

instance [Field F] : Inhabited (Expression F) where
  default := .const 0

end Airbender

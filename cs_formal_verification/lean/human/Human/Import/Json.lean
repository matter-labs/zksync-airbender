module

@[expose] public section

/- Wrappers for Rust serde types without a direct Lean counterpart (their JSON: `Serde.lean`). -/
namespace Airbender

/-- A JSON natural number with a checked upper bound. -/
structure BoundedNat (bound : Nat) where
  val : Nat
  isLt : val < bound
  deriving Repr, DecidableEq

abbrev U16 := BoundedNat 65536
abbrev U32 := BoundedNat 4294967296

/-- A Rust fixed array: a JSON array of length `n`. -/
structure Fixed (n : Nat) (α : Type) where
  values : Array α
  size_eq : values.size = n
  deriving Repr

/-- A Rust triple: a flat JSON array of three elements. -/
structure Triple (α β γ : Type) where
  first : α
  second : β
  third : γ
  deriving Repr

/-- The entries of a Rust BTreeMap, serialized as a JSON object (in the file's order). -/
structure ObjectMap (κ α : Type) where
  entries : Array (κ × α)
  deriving Repr

/-- Rust `PhantomData`, serialized as `null`. -/
inductive JsonNull where
  | null
  deriving Repr

end Airbender

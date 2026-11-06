module
public import CleanCore.Circuit.Expression

/-! # Row types of lookup tables (Clean `Clean.Circuit.Provable`, pinned 93c9d1e)

A table row type is a map `F ↦ row of F` that flattens to a fixed number of field elements. We keep
only the flattening (`size`, `toElements`, `fromElements`) and the three row types our tables use
(`field`, `fieldPair`, `fieldTriple`, `fields n`), with Clean's definitions. -/

@[expose] public section

namespace Airbender

abbrev TypeMap := Type → Type

class ProvableType (M : TypeMap) where
  size : ℕ
  toElements {F : Type} : M F → Vector F size
  fromElements {F : Type} : Vector F size → M F

export ProvableType (size toElements fromElements)

abbrev field : TypeMap := fun F => F

instance : ProvableType field where
  size := 1
  toElements x := #v[x]
  fromElements := fun ⟨⟨[x]⟩, _⟩ => x

abbrev fieldPair : TypeMap := fun F => F × F

instance (priority := high) : ProvableType fieldPair where
  size := 2
  toElements := fun (x, y) => #v[x, y]
  fromElements := fun ⟨⟨[x, y]⟩, _⟩ => (x, y)

abbrev fieldTriple : TypeMap := fun F => F × F × F

instance (priority := high) : ProvableType fieldTriple where
  size := 3
  toElements := fun (x, y, z) => #v[x, y, z]
  fromElements := fun ⟨⟨[x, y, z]⟩, _⟩ => (x, y, z)

abbrev fields (n : ℕ) : TypeMap := fun F => Vector F n

instance (priority := high) {n : ℕ} : ProvableType (fields n) where
  size := n
  toElements x := x
  fromElements v := v

/-- Evaluate every entry of a row of expressions (Clean's `ProvableType.eval`). -/
def ProvableType.eval {F : Type} [Field F] {M : TypeMap} [ProvableType M] (env : Environment F)
    (x : M (Expression F)) : M F :=
  fromElements ((toElements x).map (Expression.eval env))

end Airbender

import Airbender.Proofs.GKRProtocol.MemorySymbols

namespace Airbender.Compiler.Source
set_option warningAsError true

/-- The complete independent source tuple, with its six challenge coordinates
left as formal variables. Only placement indices are shared with the native
expression; neither source fields nor target equations come from a certificate. -/
def MemoryRow.symbolicPolynomial (row : MemoryRow) (placement : MemoryPlacement n)
    (basePlacement : Fin n → Fin m) (symbols : Compiler.MemorySymbolPlacement m) : Compiler.Polynomial m BaseField :=
  let field := fun input : MemoryField => Compiler.rename basePlacement (input.polynomial placement)
  let scaled := fun index input => Compiler.multiply (Compiler.atom (symbols.power index)) (field input)
  Compiler.add
    (Compiler.add
      (Compiler.add
        (Compiler.add
          (Compiler.add
            (Compiler.add
              (Compiler.add (Compiler.atom symbols.gamma) (field row.addressSpace))
              (scaled ⟨0, by decide⟩ row.address.low))
            (scaled ⟨1, by decide⟩ row.address.high))
          (scaled ⟨2, by decide⟩ row.timestamp.low))
        (scaled ⟨3, by decide⟩ row.timestamp.high))
      (scaled ⟨4, by decide⟩ row.data.low))
    (scaled ⟨5, by decide⟩ row.data.high)

theorem MemoryRow.symbolicPolynomial_sound [CommRing R] (row : MemoryRow)
    (placement : MemoryPlacement n) (basePlacement : Fin n → Fin m)
    (symbolPlacement : Compiler.MemorySymbolPlacement m)
    (hom : BaseField →+* R) (challenges : Compiler.CacheChallenges R)
    (symbols : Fin m → R) (base : Fin n → BaseField)
    (baseSymbols : ∀ index, symbols (basePlacement index) = hom (base index))
    (powers : ∀ index, symbols (symbolPlacement.power index) = challenges.memoryPowers index)
    (gamma : symbols symbolPlacement.gamma = challenges.memoryGamma) :
    Compiler.evaluateHom hom symbols (row.symbolicPolynomial placement basePlacement symbolPlacement) =
      row.fingerprint (placement.project base) hom challenges := by
  have field (input : MemoryField) :
      Compiler.evaluateHom hom symbols (Compiler.rename basePlacement (input.polynomial placement)) =
        hom (input.value (placement.project base)) := by
    rw [Compiler.evaluateHom_rename]
    have same : symbols ∘ basePlacement = hom ∘ base := funext baseSymbols
    rw [same, Compiler.evaluateHom_at_hom, MemoryField.polynomial_value]
  simp only [symbolicPolynomial, Compiler.evaluateHom_add, Compiler.evaluateHom_multiply,
    Compiler.evaluateHom_atom, field, powers, gamma, fingerprint]

end Airbender.Compiler.Source

import Airbender.Review.Compiler.MachineTargets

namespace Airbender.Compiler.MachineTargets

/-- A source certificate maps each parsed physical row, including padding,
into the fixed native table. It makes no claim about worker assignments. -/
def FixedSetupRows (source : String) (table : Table F (fields width)) : Prop :=
  ∀ artifact : Airbender.Setup.Artifact,
    Airbender.Setup.parse source = .ok artifact → artifact.columns.size = width →
    ∀ row : Vector F width,
      (∃ index : Fin artifact.trace_len, ∀ column : Fin width,
        row[column] = (Airbender.Setup.signedValue
          ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) →
      table.toRaw.Contains #[] row

/-- A source row needs canonical membership when a native query uses it.
The predicate retains the complete query row and its actual table tag. -/
def GuardedSetupRows (source : String) (table : Table F (fields width))
    (queried : Vector F width → Prop) : Prop :=
  ∀ artifact : Airbender.Setup.Artifact,
    Airbender.Setup.parse source = .ok artifact → artifact.columns.size = width →
    ∀ row : Vector F width,
      (∃ index : Fin artifact.trace_len, ∀ column : Fin width,
        row[column] = (Airbender.Setup.signedValue
          ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) →
      queried row → table.toRaw.Contains #[] row

end Airbender.Compiler.MachineTargets

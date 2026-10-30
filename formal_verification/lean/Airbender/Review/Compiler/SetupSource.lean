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

end Airbender.Compiler.MachineTargets

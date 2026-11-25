module
public import Human.Circuits.UnifiedReduced.Proth120Artifact
public import Human.Circuits.UnifiedReduced.Modular

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Arithmetic

export Modular (wordAt)

/-- The unified wrap's modular rows compute the RV32 BabyBear operation, including the old destination for FMA. -/
def ModularResultClaim : Prop := Modular.ResultSoundness proth120Modulus importedConstraints

/-- An active modular row satisfies the result theorem's premises. -/
def ModularResultSatisfiableClaim : Prop := Modular.RowSatisfiable proth120Modulus importedConstraints

end Airbender.UnifiedReduced.Proth120

module
public import Proven.NonVacuous.UnrolledNative.Model
public import Proven.Compiler.CPUWitnesses.AddSub.Data

@[expose] public section
namespace Airbender.NonVacuous.UnrolledNative
open Compiler
set_option warningAsError true

/-- Every actual native ADD tuple equals its public fixed or decoder row. -/
theorem lookup_check : CPUWitnesses.AddSub.canonicalCheck PooledBoot.initial program
    PooledBoot.assignment = true := by
  kernel_rfl

end Airbender.NonVacuous.UnrolledNative

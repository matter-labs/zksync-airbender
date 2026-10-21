import Tests.SubwordBoundsPart0
import Tests.SubwordBoundsPart6
import Tests.SubwordBoundsPart7

namespace Tests.SubwordBoundsRows
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordBoundsWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem native_constraints : ∀ sample : Fin 8,
    FlatOperation.ConstraintsHoldFlat (environment (assignment sample))
      (SubwordMemory.importedConstraints rom)
  | 0 => Tests.SubwordBoundsPart0.constraints_0
  | 1 => unchanged_constraints ⟨1,by decide⟩ (by decide) (by decide) (by decide)
  | 2 => unchanged_constraints ⟨2,by decide⟩ (by decide) (by decide) (by decide)
  | 3 => unchanged_constraints ⟨3,by decide⟩ (by decide) (by decide) (by decide)
  | 4 => unchanged_constraints ⟨4,by decide⟩ (by decide) (by decide) (by decide)
  | 5 => unchanged_constraints ⟨5,by decide⟩ (by decide) (by decide) (by decide)
  | 6 => Tests.SubwordBoundsPart6.constraints_6
  | 7 => Tests.SubwordBoundsPart7.constraints_7

end Tests.SubwordBoundsRows

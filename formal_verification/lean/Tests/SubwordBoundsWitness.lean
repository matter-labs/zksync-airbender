import Tests.SubwordHistoryRows

namespace Tests.SubwordBoundsWitness
open Airbender Verification Arithmetic Trace SubwordMemory
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

abbrev rom := Tests.SubwordDecoderFixture.rom

/-- Bind ROM-shadow reads at address zero to the actual public instruction
    bytes. Other old native rows and every dynamic query remain unchanged. -/
def values0 : Array Nat := #[0,0,4,0,1,1,0,3,0,0,0,0,0,4,0,8,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,33155,0,1,3,0,0,0,65534,65535,33022,4660,33022,65534,65535,33155,0,98556,0,98556,0,0,33022,4660,46,33022,65534,65535,45,65534,65535,65534,65535,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
def values6 : Array Nat := #[0,0,4,0,1,1,0,3,0,0,0,4,0,4,0,8,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,49539,0,1,3,0,0,0,254,0,33022,4660,33022,254,0,49539,0,33276,0,33276,0,0,33022,4660,46,1081598,254,0,45,254,0,254,0,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
def values7 : Array Nat := #[0,0,4,0,1,1,0,1,0,0,0,0,0,4,0,8,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,32899,0,1,1,0,0,0,65534,65535,33022,4660,33022,65534,65535,32899,0,98556,0,98556,0,0,33022,4660,46,33022,65534,65535,45,65534,65535,65534,65535,1227138194,0,2147450879,0,0,0,1,0,0,1,4,0,1,0]

def assignment (sample : Fin 8) (column : Nat) : ZMod mersenne31Modulus :=
  if sample.val = 0 then (values0[column]?.getD 0 : Nat)
  else if sample.val = 6 then (values6[column]?.getD 0 : Nat)
  else if sample.val = 7 then (values7[column]?.getD 0 : Nat)
  else Tests.SubwordHistoryRows.assignment sample column

/-- Transport unchanged native rows before specializing the finite sample.
    This avoids repeatedly normalizing full closed table-containing relations. -/
theorem unchanged_constraints (sample : Fin 8)
    (zero : sample.val ≠ 0) (six : sample.val ≠ 6) (seven : sample.val ≠ 7) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment sample))
      (SubwordMemory.importedConstraints rom) := by
  have same : assignment sample = Tests.SubwordHistoryRows.assignment sample := by
    funext column
    simp only [assignment,zero,six,seven,ite_false]
  exact (congrArg (fun f => FlatOperation.ConstraintsHoldFlat (environment f)
    (SubwordMemory.importedConstraints rom)) same).mpr
    (Tests.SubwordHistoryRows.native_constraints sample)

end Tests.SubwordBoundsWitness

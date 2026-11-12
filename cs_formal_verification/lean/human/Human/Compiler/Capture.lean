module
public import Human.Import.Schema

@[expose] public section

namespace Airbender.Compiler

/-- Source inputs outside the arithmetic compiler capture. -/
structure RemainingInputs where
  /-- The source has a delegation state interface. -/
  delegation : Bool
  /-- The source has an executor state interface. -/
  executor : Bool
  /-- The number of source lookup queries. -/
  lookups : Nat
  /-- The number of source memory queries. -/
  memory_queries : Nat
  /-- The number of source range checks. -/
  range_checks : Nat
  /-- The number of source register and indirect accesses. -/
  register_and_indirect_accesses : Nat

/-- Source arithmetic before the compiler lowers it to GKR layers. -/
structure SourceSnapshot where
  /-- Source variables declared Boolean. -/
  booleans : Array Nat
  /-- The source variable and layer pairs. -/
  layers : Array (Nat × Nat)
  /-- The source variable count. -/
  num_variables : Nat
  /-- Counts of the source interfaces that need separate preservation. -/
  remaining_inputs : RemainingInputs
  /-- The source arithmetic expressions and sparse constraints. -/
  statements : Array StructuredStatement

/-- A native source/compiler capture. Coefficients retain their serialized Montgomery representation. -/
structure NativeCapture where
  /-- The compiler used cached layers. -/
  cached : Bool
  /-- The complete compiled artifact. -/
  circuit : Circuit
  /-- The exporter selected this circuit family. -/
  family : String
  /-- The exporter format version. -/
  format_version : Nat
  /-- The arithmetic snapshot taken before compilation. -/
  source : SourceSnapshot

end Airbender.Compiler

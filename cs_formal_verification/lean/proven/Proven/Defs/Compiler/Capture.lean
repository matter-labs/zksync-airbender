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

/-- The source capture read by certificate generation. -/
structure SourceCapture where
  cached : Bool
  family : String
  format_version : Nat
  source : SourceSnapshot

end Airbender.Compiler

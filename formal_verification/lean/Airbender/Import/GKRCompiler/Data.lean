import Airbender.Import.Schema
import Mathlib.Data.ZMod.Basic
import Lean

namespace Airbender.Compiler.Import
open Lean
set_option warningAsError true

structure RemainingInputs where
  delegation : Bool
  executor : Bool
  lookups : Nat
  memory_queries : Nat
  range_checks : Nat
  register_and_indirect_accesses : Nat
  deriving FromJson

structure Source where
  num_variables : Nat
  statements : Array StructuredStatement
  booleans : Array Nat
  layers : Array (Nat × Nat)
  remaining_inputs : RemainingInputs
  deriving FromJson

structure Pair where
  format_version : Nat
  family : String
  cached : Bool
  source : Source
  circuit : Circuit
  deriving FromJson

abbrev EncodedPolynomial := Array (Nat × Array Nat)
abbrev EncodedCombination := Array (EncodedPolynomial × Nat)

structure IdentityCertificate where
  format_version : Nat
  addresses : Array GKRAddress
  selected : Array Nat
  extension : Array EncodedPolynomial
  backward : Array EncodedCombination
  forward : Array EncodedCombination
  deriving FromJson

end Airbender.Compiler.Import

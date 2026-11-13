module
public import Human.Import.CompilerJson
public import Human.Compiler.Capture
public import Mathlib.Data.ZMod.Basic
public import Lean
public meta import Human.Import.CompilerJson
public meta import Human.Compiler.Capture
public meta import Mathlib.Data.ZMod.Basic
public meta import Lean

public meta section
set_option warningAsError true

namespace Airbender.Compiler.Import
open Lean

abbrev RemainingInputs := Airbender.Compiler.RemainingInputs
abbrev Source := SourceSnapshot
abbrev Pair := NativeCapture

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

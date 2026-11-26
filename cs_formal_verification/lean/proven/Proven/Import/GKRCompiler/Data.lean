module
public import Proven.Import.CompilerJson
public import Proven.Defs.Compiler.Capture
public import Human.Import.Transcribe
public import Mathlib.Data.ZMod.Basic
public import Lean
public meta import Proven.Import.CompilerJson
public meta import Proven.Defs.Compiler.Capture
public meta import Human.Import.Transcribe
public meta import Mathlib.Data.ZMod.Basic
public meta import Lean

public meta section
set_option warningAsError true

namespace Airbender.Compiler.Import
open Lean

abbrev RemainingInputs := Airbender.Compiler.RemainingInputs
abbrev Source := SourceSnapshot
structure Pair extends SourceCapture where
  circuit : Circuit

/-- The production layout file for each captured source family. -/
def cachedLayout : String → Option String
  | "add-sub" => some "circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop/generated/layout.json"
  | "bigint" => some "circuit_defs/bigint_with_control/generated/layout.json"
  | "blake-g" => some "circuit_defs/blake2_g_function/generated/layout.json"
  | "blake-round" => some "circuit_defs/blake2_with_compression/generated/layout.json"
  | "jump-branch" => some "circuit_defs/unrolled_circuits/jump_branch_slt/generated/layout.json"
  | "keccak" => some "circuit_defs/keccak_special5/generated/layout.json"
  | "mul-div" => some "circuit_defs/unrolled_circuits/mul_div_unsigned/generated/layout.json"
  | "shift-binop" => some "circuit_defs/unrolled_circuits/shift_binary/generated/layout.json"
  | "subword-memory" => some "circuit_defs/unrolled_circuits/load_store_subword_only/generated/layout.json"
  | "unified" => some "circuit_defs/unrolled_circuits/unified_reduced_machine/generated/layout.json"
  | "word-memory" => some "circuit_defs/unrolled_circuits/load_store_word_only/generated/layout.json"
  | "keccak-column-parity" => some "circuit_defs/keccak_column_parity/generated/layout.json"
  | "keccak-theta-rho" => some "circuit_defs/keccak_theta_rho/generated/layout.json"
  | "keccak-chi5" => some "circuit_defs/keccak_chi5/generated/layout.json"
  | _ => none

/-- Read the source snapshot and decode its production circuit with the proved parser. -/
def parsePairJson (json : Lean.Json) : IO (Except String Pair) := do
  let snapshot : SourceCapture ← match fromJson? json with
    | .ok snapshot => pure snapshot
    | .error reason => return .error reason
  unless snapshot.format_version == 1 && snapshot.cached do
    return .error "Expected a format-1 cached source snapshot"
  let some layout := cachedLayout snapshot.family
    | return .error s!"Unsupported source family: {snapshot.family}"
  let text ← IO.FS.readFile s!"../../{layout}"
  match parseCircuit text with
  | .error reason => return .error reason
  | .ok circuit => return .ok { toSourceCapture := snapshot, circuit }

/-- Parse source JSON before loading its production circuit. -/
def parsePairText (text : String) : IO (Except String Pair) := do
  match Lean.Json.parse text with
  | .error reason => return .error reason
  | .ok json => parsePairJson json

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

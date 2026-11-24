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
  | "add-sub" => some "add_sub_lui_auipc_mop"
  | "bigint" => some "bigint_with_extended_control"
  | "blake-g" => some "blake2_g_function"
  | "blake-round" => some "blake2_with_extended_control"
  | "jump-branch" => some "jump_branch_slt"
  | "keccak" => some "keccak_special5"
  | "mul-div" => some "unsigned_mul_div"
  | "shift-binop" => some "shift_binop"
  | "subword-memory" => some "mem_subword_only"
  | "unified" => some "unified_reduced_machine"
  | "word-memory" => some "mem_word_only"
  | "keccak-column-parity" => some "keccak_column_parity"
  | "keccak-theta-rho" => some "keccak_theta_rho"
  | "keccak-chi5" => some "keccak_chi5"
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
  let text ← IO.FS.readFile s!"../../cs/compiled_circuits/{layout}_layout_gkr.json"
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

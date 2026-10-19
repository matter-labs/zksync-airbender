import Airbender.Import.Schema
import Airbender.Import.Coefficients

namespace Airbender.Setup
open Lean

/-- Lossless blocks of actual canonical field values, not table-generation rules. -/
inductive Block where
  | affine (length first : Nat) (step : Int)
  | dense (values : Array Nat)
  | periodic (repetitions : Nat) (stride : Int) (values : Array Nat)
  deriving Repr, DecidableEq

private def exactKeys (json : Json) (keys : Array String) : Except String Unit := do
  let entries := (← json.getObj?).toArray
  unless entries.size == keys.size && entries.all (fun (key, _) => keys.contains key) do
    throw "unexpected or missing setup JSON fields"

instance : FromJson Block where
  fromJson? json := do
    let kind : String ← fromJson? (← json.getObjVal? "kind")
    match kind with
    | "affine" =>
      exactKeys json #["kind", "length", "first", "step"]
      return .affine (← fromJson? (← json.getObjVal? "length"))
        (← fromJson? (← json.getObjVal? "first")) (← fromJson? (← json.getObjVal? "step"))
    | "dense" =>
      exactKeys json #["kind", "values"]
      return .dense (← fromJson? (← json.getObjVal? "values"))
    | "periodic" =>
      exactKeys json #["kind", "repetitions", "stride", "values"]
      return .periodic (← fromJson? (← json.getObjVal? "repetitions"))
        (← fromJson? (← json.getObjVal? "stride")) (← fromJson? (← json.getObjVal? "values"))
    | _ => throw "unknown setup column encoding"

def Block.length : Block → Nat
  | .affine length _ _ => length
  | .dense values => values.size
  | .periodic repetitions _ values => repetitions * values.size

def Block.get? (block : Block) (index : Nat) : Option Nat :=
  if index < block.length then
    match block with
    | .affine _ first step =>
      let value := (first : Int) + step * index
      if 0 ≤ value then some value.toNat else none
    | .dense values => values[index]?
    | .periodic _ stride values =>
      let value := ((values[index % values.size]?.getD 0 : Nat) : Int) + stride * (index / values.size)
      if 0 ≤ value then some value.toNat else none
  else none

structure Column where
  blocks : Array Block
  deriving Repr, DecidableEq, FromJson

def getFromBlocks : List Block → Nat → Option Nat
  | [], _ => none
  | block :: rest, index =>
    if index < block.length then block.get? index
    else getFromBlocks rest (index - block.length)

def Column.get? (column : Column) (index : Nat) : Option Nat :=
  getFromBlocks column.blocks.toList index

def Column.validate (column : Column) (length bound : Nat) : Except String Unit := do
  let mut covered := 0
  for block in column.blocks do
    unless 0 < block.length do throw "empty setup column block"
    covered := covered + block.length
    unless covered ≤ length do throw "setup column exceeds its domain"
    match block with
    | .affine _ first step =>
      unless first < 4294967296 && -9223372036854775808 ≤ step && step < 9223372036854775808 do
        throw "setup affine encoding exceeds Rust integer bounds"
      for index in #[0, block.length - 1] do
        let some value := block.get? index | throw "negative setup column value"
        unless value < bound do throw "noncanonical setup field element"
    | .dense values =>
      unless values.all (· < bound) do throw "noncanonical setup field element"
    | .periodic repetitions stride values =>
      unless -9223372036854775808 ≤ stride && stride < 9223372036854775808 do
        throw "setup periodic encoding exceeds Rust integer bounds"
      for first in values do
        let last := (first : Int) + stride * (repetitions - 1)
        unless first < bound && 0 ≤ last && last < bound do
          throw "noncanonical setup field element"
  unless covered == length do throw "setup column does not cover its domain"

/-- Local rows of a native table/materializer output, before physical trace assembly. -/
structure Matrix where
  length : Nat
  columns : Array Column
  deriving Repr, FromJson

structure Region where
  id : Nat
  offset : Nat
  data : Matrix
  deriving Repr, FromJson

structure Program where
  image_words : Nat
  image : Column
  text_words : Nat
  text : Column
  deriving Repr, FromJson

structure Artifact where
  version : Nat
  field_modulus : Nat
  family : String
  program : Program
  generic_rows : Nat
  tables : Array Region
  decoder : Matrix
  range16 : Matrix
  deriving Repr, FromJson

private def Matrix.validate (matrix : Matrix) (length width : Nat) : Except String Unit := do
  unless matrix.length == length && matrix.columns.size == width do
    throw "unexpected native setup matrix geometry"
  for column in matrix.columns do column.validate length mersenne31Modulus

def Artifact.validate (artifact : Artifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.family == "load_store_word_only" do throw "unsupported native setup profile"
  unless artifact.program.image_words == 1048576 && artifact.program.text_words ≤ 1048576 do
    throw "unexpected native program extent"
  artifact.program.image.validate artifact.program.image_words 4294967296
  artifact.program.text.validate artifact.program.text_words 4294967296
  unless artifact.generic_rows == 1114113 && artifact.tables.size == 3 do
    throw "unexpected native generic table extent"
  for (region, (id, offset, length)) in artifact.tables.zip #[(0, 0, 1), (23, 1, 65536), (24, 65537, 1048576)] do
    unless region.id == id && region.offset == offset do throw "unexpected native table region"
    region.data.validate length 4
  artifact.decoder.validate 1048576 10
  artifact.range16.validate 65536 1

private def columnKeys (json : Json) : Except String Unit := exactKeys json #["blocks"]
private def matrixKeys (json : Json) : Except String Unit := do
  exactKeys json #["length", "columns"]
  for column in (← (← json.getObjVal? "columns").getArr?) do columnKeys column

def parse (source : String) : Except String Artifact := do
  let json ← Json.parse source
  exactKeys json #["version", "field_modulus", "family", "program", "generic_rows", "tables", "decoder", "range16"]
  let program ← json.getObjVal? "program"
  exactKeys program #["image_words", "image", "text_words", "text"]
  columnKeys (← program.getObjVal? "image")
  columnKeys (← program.getObjVal? "text")
  for region in (← (← json.getObjVal? "tables").getArr?) do
    exactKeys region #["id", "offset", "data"]
    matrixKeys (← region.getObjVal? "data")
  matrixKeys (← json.getObjVal? "decoder")
  matrixKeys (← json.getObjVal? "range16")
  let artifact : Artifact ← fromJson? json
  artifact.validate
  return artifact

/-- Program-independent native scalar prefixes. Physical zero padding and the
    reserved normalization row are separate from these exported local values. -/
structure ScalarArtifact where
  version : Nat
  field_modulus : Nat
  profile : String
  range16 : Matrix
  timestamp19 : Matrix
  deriving Repr, FromJson

def ScalarArtifact.validate (artifact : ScalarArtifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.profile == "range16_timestamp19" do throw "unsupported native scalar profile"
  artifact.range16.validate 65536 1
  artifact.timestamp19.validate 524288 1

def parseScalars (source : String) : Except String ScalarArtifact := do
  let json ← Json.parse source
  exactKeys json #["version", "field_modulus", "profile", "range16", "timestamp19"]
  matrixKeys (← json.getObjVal? "range16")
  matrixKeys (← json.getObjVal? "timestamp19")
  let artifact : ScalarArtifact ← fromJson? json
  artifact.validate
  return artifact

/-- Decoder preprocessing is separate from generic/scalar table assembly.
    Each profile records the actual native family, including arithmetic custom MOPs;
    each semantic certificate states which public input it covers. -/
structure DecoderArtifact where
  version : Nat
  field_modulus : Nat
  family : String
  text_words : Nat
  text : Column
  decoder : Matrix
  deriving Repr, FromJson

private def validateDecoder (family : String) (artifact : DecoderArtifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.family == family do throw "unsupported native decoder profile"
  unless artifact.text_words ≤ 1048576 do throw "unexpected native text extent"
  artifact.text.validate artifact.text_words 4294967296
  artifact.decoder.validate 1048576 10

def DecoderArtifact.validate (artifact : DecoderArtifact) : Except String Unit :=
  validateDecoder "add_sub_lui_auipc_mop" artifact

private def parseDecoderFor (family source : String) : Except String DecoderArtifact := do
  let json ← Json.parse source
  exactKeys json #["version", "field_modulus", "family", "text_words", "text", "decoder"]
  columnKeys (← json.getObjVal? "text")
  matrixKeys (← json.getObjVal? "decoder")
  let artifact : DecoderArtifact ← fromJson? json
  validateDecoder family artifact
  return artifact

/-- The arithmetic entry point retains its exact original family guard. -/
def parseDecoder (source : String) : Except String DecoderArtifact :=
  parseDecoderFor "add_sub_lui_auipc_mop" source

/-- Separate signed native control profile; unsigned-only profiles fail closed. -/
def parseControlDecoder (source : String) : Except String DecoderArtifact :=
  parseDecoderFor "jump_branch_slt_signed" source

/-- A tiny direct native API export, separate from regional prefix artifacts. -/
structure DecoderPaddingArtifact where
  version : Nat
  field_modulus : Nat
  profile : String
  row : Array Nat
  deriving Repr, FromJson

def DecoderPaddingArtifact.validate (artifact : DecoderPaddingArtifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.profile == "decoder_padding" do throw "unsupported native decoder padding profile"
  unless artifact.row.size == 10 && artifact.row.all (· < mersenne31Modulus) do
    throw "invalid native decoder padding row"

def parseDecoderPadding (source : String) : Except String DecoderPaddingArtifact := do
  let json ← Json.parse source
  exactKeys json #["version", "field_modulus", "profile", "row"]
  let artifact : DecoderPaddingArtifact ← fromJson? json
  artifact.validate
  return artifact

/-- Exact regional fixed tables registered by the native control-flow family. -/
structure ControlArtifact where
  version : Nat
  field_modulus : Nat
  profile : String
  generic_rows : Nat
  tables : Array Region
  deriving Repr, FromJson

def ControlArtifact.validate (artifact : ControlArtifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.profile == "jump_branch_slt_fixed" do throw "unsupported native control table profile"
  unless artifact.generic_rows == 65664 && artifact.tables.size == 2 do
    throw "unexpected native control table extent"
  for (region, (id, offset, length)) in artifact.tables.zip #[(17, 0, 65536), (43, 65536, 128)] do
    unless region.id == id && region.offset == offset do throw "unexpected native control region"
    region.data.validate length 4

def parseControl (source : String) : Except String ControlArtifact := do
  let json ← Json.parse source
  exactKeys json #["version", "field_modulus", "profile", "generic_rows", "tables"]
  for region in (← (← json.getObjVal? "tables").getArr?) do
    exactKeys region #["id", "offset", "data"]
    matrixKeys (← region.getObjVal? "data")
  let artifact : ControlArtifact ← fromJson? json
  artifact.validate
  return artifact
/-- The same strict regional envelope as control tables, with its own profile.
    This imports only actual unsigned mul/div fixed rows, not decoder semantics. -/
def parseSmallRange (source : String) : Except String ControlArtifact := do
  let json ← Json.parse source
  exactKeys json #["version", "field_modulus", "profile", "generic_rows", "tables"]
  for region in (← (← json.getObjVal? "tables").getArr?) do
    exactKeys region #["id", "offset", "data"]
    matrixKeys (← region.getObjVal? "data")
  let artifact : ControlArtifact ← fromJson? json
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.profile == "unsigned_mul_div_fixed" do throw "unsupported native byte-table profile"
  unless artifact.generic_rows == 65536 && artifact.tables.size == 1 do
    throw "unexpected native byte-table extent"
  let some region := artifact.tables[0]? | throw "missing native byte table"
  unless region.id == 8 && region.offset == 0 do throw "unexpected native byte-table region"
  region.data.validate 65536 4
  return artifact


def DecoderArtifact.validateShift (artifact : DecoderArtifact) : Except String Unit :=
  validateDecoder "shift_binop_csrrw" artifact

def parseShiftDecoder (source : String) : Except String DecoderArtifact :=
  parseDecoderFor "shift_binop_csrrw" source

/-- A strict actual native zero/XOR/OR/AND prefix, not the complete shift family. -/
def ControlArtifact.validateBinary (artifact : ControlArtifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.profile == "shift_binop_binary_prefix" do throw "unsupported native binary prefix"
  unless artifact.generic_rows == 196609 && artifact.tables.size == 4 do
    throw "unexpected native binary prefix extent"
  for (region, (id, offset, length)) in artifact.tables.zip #[(0,0,1),(4,1,65536),(6,65537,65536),(7,131073,65536)] do
    unless region.id == id && region.offset == offset do throw "unexpected native binary prefix region"
    region.data.validate length 4

def parseBinary (source : String) : Except String ControlArtifact := do
  let json ← Json.parse source
  exactKeys json #["version", "field_modulus", "profile", "generic_rows", "tables"]
  for region in (← (← json.getObjVal? "tables").getArr?) do
    exactKeys region #["id", "offset", "data"]
    matrixKeys (← region.getObjVal? "data")
  let artifact : ControlArtifact ← fromJson? json
  artifact.validateBinary
  return artifact

/-- Selected scalar/sign-fill regions, not a contiguous prefix or full family.
    Offsets retain the actual compiled layout, including unexported regions. -/
def ControlArtifact.validateShiftScalars (artifact : ControlArtifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.profile == "shift_binop_scalar_regions" do throw "unsupported native shift scalar profile"
  unless artifact.generic_rows == 2228224 && artifact.tables.size == 3 do
    throw "unexpected native shift scalar extent"
  for (region, (id, offset, length)) in artifact.tables.zip
      #[(47,200705,65536),(52,8654849,2097152),(53,10752001,65536)] do
    unless region.id == id && region.offset == offset do throw "unexpected native shift scalar region"
    region.data.validate length 4

def parseShiftScalars (source : String) : Except String ControlArtifact := do
  let json ← Json.parse source
  exactKeys json #["version", "field_modulus", "profile", "generic_rows", "tables"]
  for region in (← (← json.getObjVal? "tables").getArr?) do
    exactKeys region #["id", "offset", "data"]
    matrixKeys (← region.getObjVal? "data")
  let artifact : ControlArtifact ← fromJson? json
  artifact.validateShiftScalars
  return artifact

/-- Actual native low-input SRL rows, retaining their full compiled placement. -/
def ControlArtifact.validateSrlLow (artifact : ControlArtifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.profile == "shift_binop_srl_low" do throw "unsupported native SRL-low profile"
  unless artifact.generic_rows == 2097152 && artifact.tables.size == 1 do
    throw "unexpected native SRL-low extent"
  let some region := artifact.tables[0]? | throw "missing native SRL-low table"
  unless region.id == 50 && region.offset == 4460545 do throw "unexpected native SRL-low region"
  region.data.validate 2097152 4

def parseSrlLow (source : String) : Except String ControlArtifact := do
  let json ← Json.parse source
  exactKeys json #["version", "field_modulus", "profile", "generic_rows", "tables"]
  for region in (← (← json.getObjVal? "tables").getArr?) do
    exactKeys region #["id", "offset", "data"]
    matrixKeys (← region.getObjVal? "data")
  let artifact : ControlArtifact ← fromJson? json
  artifact.validateSrlLow
  return artifact

end Airbender.Setup

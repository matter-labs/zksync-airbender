import Airbender.Import.Setup

namespace Airbender.Setup.ReducedFixed
open Lean

structure Public where
  image_words : Nat
  image : Column
  delegation_csrs : Array Nat
  allow_non_determinism : Bool
  deriving Repr, FromJson

structure Artifact where
  version : Nat
  field_modulus : Nat
  profile : String
  generic_rows : Nat
  «public» : Public
  tables : Array Region
  deriving Repr, FromJson

/-- Regenerated native v2 registry, including its actual truncation region. -/
def regions : Array (Nat × Nat × Nat) :=
  #[(0,0,1),(4,1,65536),(6,65537,65536),(7,131073,65536),
    (16,196609,65536),(17,262145,65536),(18,327681,65536),
    (20,393217,128),(22,393345,128),(23,393473,65536),
    (24,459009,1048576),(25,1507585,4096),(37,1511681,4194304),
    (47,5705985,65536)]

private def exactKeys (json : Json) (keys : Array String) : Except String Unit := do
  let entries := (← json.getObj?).toArray
  unless entries.size == keys.size && entries.all (fun (key, _) => keys.contains key) do
    throw "unexpected or missing native reduced fixed JSON fields"

def Artifact.validate (artifact : Artifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.profile == "reduced_machine_fixed" do
    throw "unsupported native reduced fixed profile"
  unless artifact.generic_rows == 5771521 && artifact.tables.size == regions.size do
    throw "unsupported native reduced fixed extent"
  unless artifact.«public».image_words ≤ 1048576 && artifact.«public».allow_non_determinism &&
      artifact.«public».delegation_csrs.all (· < 4096) do
    throw "unsupported native reduced public inputs"
  artifact.«public».image.validate artifact.«public».image_words 4294967296
  for (region,(id,offset,length)) in artifact.tables.zip regions do
    unless region.id == id && region.offset == offset && region.data.length == length &&
        region.data.columns.size == 4 do
      throw "unsupported native reduced fixed region geometry"
    for column in region.data.columns do column.validate length mersenne31Modulus

/-- Geometry and literal canonicality only; row semantics are kernel obligations. -/
def parse (source : String) : Except String Artifact := do
  let json ← Json.parse source
  exactKeys json #["version","field_modulus","profile","generic_rows","public","tables"]
  let inputs ← json.getObjVal? "public"
  exactKeys inputs #["image_words","image","delegation_csrs","allow_non_determinism"]
  exactKeys (← inputs.getObjVal? "image") #["blocks"]
  for region in (← (← json.getObjVal? "tables").getArr?) do
    exactKeys region #["id","offset","data"]
    let data ← region.getObjVal? "data"
    exactKeys data #["length","columns"]
    for column in (← (← data.getObjVal? "columns").getArr?) do
      exactKeys column #["blocks"]
  let artifact : Artifact ← fromJson? json
  artifact.validate
  return artifact

end Airbender.Setup.ReducedFixed

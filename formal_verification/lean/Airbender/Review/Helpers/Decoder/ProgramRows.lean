import Airbender.Review.Helpers.Decoder.ModularExternal

namespace Airbender.Trace.NativeDecoder.ProgramRows
open Reference.RiscV.Sail Reference.Sail

/-- The two Rust preprocessing configurations used by the unrolled setup
machines. This is a Lean model; equality to Rust output needs a differential
test for every admitted public program. -/
inductive Config where
  | fullUnsigned | reduced
  deriving DecidableEq

def Config.fields (config : Config) :
    SailRV32.instruction → Option (DecoderData PooledFamily) :=
  match config with
  | .fullUnsigned => AddSub.Modular.External.decoderFields
  | .reduced => fun instruction =>
      (AddSub.Modular.External.decoderFields instruction).filter fun data =>
        match data.family with
        | .addSub | .jumpBranchSlt | .shiftBinop | .wordMemory => true
        | .mulDiv | .subwordMemory => false

/-- Decode one public text word at its native byte PC. Unsupported words have
no entry. The original Sail instruction and native-family projection remain
visible in the entry, independently of witness values. -/
def wordEntry (config : Config) (initial : State) (bits : BitVec 32)
    (index : Nat) : Option PooledProgramEntry := do
  let instruction ← match run (SailRV32.Functions.encdec_backwards bits) initial with
    | .ok instruction _ => some instruction
    | .error _ _ => none
  let data ← config.fields instruction
  pure ⟨BitVec.ofNat 32 (4 * index), bits, instruction, data⟩

/-- Public entries for all supported words; unsupported encodings are retained
as holes in the row function below, rather than rejecting the whole program. -/
def programOf (config : Config) (initial : State) (text : List (BitVec 32)) :
    List PooledProgramEntry :=
  text.zipIdx.filterMap fun (bits, index) => wordEntry config initial bits index

/-- Rust uses minus one in every selected column for an unsupported word. -/
def sentinel {p : Nat} : Vector (ZMod p) 9 :=
  #v[-1, -1, -1, -1, -1, -1, -1, -1, -1]

def familyRow {p : Nat} (config : Config) (initial : State)
    (family : PooledFamily) (bits : BitVec 32) (index : Nat) :
    Vector (ZMod p) 9 :=
  match wordEntry config initial bits index with
  | some entry => if entry.data.family = family then entry.query else sentinel
  | none => sentinel

/-- One row per public word index, followed by unsupported padding up to the
native ROM capacity. -/
def rows {p : Nat} (config : Config) (initial : State)
    (text : List (BitVec 32)) (capacity : Nat)
    (_fits : text.length ≤ capacity) (family : PooledFamily) :
    List (Vector (ZMod p) 9) :=
  text.zipIdx.map (fun (bits, index) => familyRow config initial family bits index) ++
    List.replicate (capacity - text.length) sentinel

/-- The native setup keeps precisely the columns selected by its circuit mask,
in their original order. A mask has the full nine-column width and selects both
PC limbs, as required by Rust's materializer. -/
structure Mask where
  columns : Array Bool
  width : columns.size = 9
  pcLow : columns[0]?.getD false = true
  pcHigh : columns[1]?.getD false = true

def maskRow {p : Nat} (mask : Mask) (row : Vector (ZMod p) 9) : List (ZMod p) :=
  row[0] :: row[1] ::
  ((mask.columns.toList.drop 2).zip (row.toList.drop 2)).filterMap fun (selected, value) =>
    if selected then some value else none

/-- Program-dependent decoder columns, including unsupported and padded rows.
The remaining premise for a native circuit is equality of its imported setup
columns to these rows; this definition alone does not assert that equality. -/
def nativeDecoderRows {p : Nat} (config : Config) (initial : State)
    (text : List (BitVec 32)) (capacity : Nat)
    (fits : text.length ≤ capacity) (family : PooledFamily) (mask : Mask) :
    List (List (ZMod p)) :=
  (rows config initial text capacity fits family).map (maskRow mask)

end Airbender.Trace.NativeDecoder.ProgramRows

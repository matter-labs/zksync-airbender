module
public import Human.Import.Transcribe
public meta import Human.Import.Transcribe
public import Lean
public meta import Lean

public meta section

/-! # TRUSTED: review. `import_circuit`: an artifact JSON as a Lean constant

`import_circuit name from "path"` reads the file (Lake tracks it through the `needs` input of the library that
uses the command), decodes it (`parseCircuit`, `Transcribe.lean`) and adds two definitions, built directly as
kernel terms:
* `nameSourceBytes : String`, the file's text (also compiled, for the regression tests);
* `name : Circuit`, the decoded artifact, reflected constructor by constructor (`ToExpr`: derived for the schema
  types, by hand below for the two types that carry a proof).
The kernel checks that `name` is a well-typed `Circuit`; that it is the decoding of the text is this file's
responsibility, unless the artifact's claims also state it. With `bytes`, the command also adds
* `nameBytes : ByteArray`, the file's bytes, for a claim that the kernel evaluates
  (`Json.parse nameBytes >>= Circuit.decode = .ok name`); then only the file read is trusted. -/

namespace Airbender
open Lean Elab Command

/-- Quote an array as its constructor, without a kernel-side list conversion. -/
instance (priority := 1100) {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (Array α) where
  toExpr values :=
    mkApp2 (mkConst ``Array.mk [toLevel.{u}]) (toTypeExpr α) (toExpr values.toList)
  toTypeExpr := mkApp (mkConst ``Array [toLevel.{u}]) (toTypeExpr α)

/-- `⟨n, proof of n < b by evaluation⟩`. -/
instance {b : Nat} : ToExpr (BoundedNat b) where
  toExpr n :=
    let lt := mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat) (mkNatLit n.val) (mkNatLit b)
    mkApp3 (mkConst ``BoundedNat.mk) (mkNatLit b) (mkNatLit n.val)
      (mkApp3 (mkConst ``of_decide_eq_true) lt (mkApp2 (mkConst ``Nat.decLt) (mkNatLit n.val) (mkNatLit b))
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)))
  toTypeExpr := mkApp (mkConst ``BoundedNat) (mkNatLit b)

/-- `⟨values, proof that values.size = n by evaluation⟩`. -/
instance {n : Nat} {α : Type} [ToExpr α] : ToExpr (Fixed n α) where
  toExpr a := mkApp4 (mkConst ``Fixed.mk) (mkNatLit n) (toTypeExpr α) (toExpr a.values)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit n))
  toTypeExpr := mkApp2 (mkConst ``Fixed) (mkNatLit n) (toTypeExpr α)

deriving instance ToExpr for Triple
deriving instance ToExpr for ObjectMap
deriving instance ToExpr for JsonNull
deriving instance ToExpr for Coefficient
deriving instance ToExpr for ColumnRange
deriving instance ToExpr for OutputType
deriving instance ToExpr for VirtualSetupPoly
deriving instance ToExpr for GKRAddress
deriving instance ToExpr for LinearRelation
deriving instance ToExpr for SingleColumnLookupRelation
deriving instance ToExpr for VectorLookupRelation
deriving instance ToExpr for CompiledMaxQuadraticGKRRelation
deriving instance ToExpr for CompiledAddressSpaceRelationStrict
deriving instance ToExpr for CompiledAddressStrict
deriving instance ToExpr for CompiledMemoryTimestamp
deriving instance ToExpr for RamWordRepresentation
deriving instance ToExpr for SpecialMemoryContributionRelation
deriving instance ToExpr for MaxQuadraticConstraintsGKRRelation
deriving instance ToExpr for InitsOrTeardownsTimestampAndValue
deriving instance ToExpr for StructuredExpression
deriving instance ToExpr for GKRRelation
deriving instance ToExpr for GKRCacheRelation
deriving instance ToExpr for GateArtifacts
deriving instance ToExpr for RamAuxComparisonSet
deriving instance ToExpr for RelativeTimestampGroup
deriving instance ToExpr for GKRAuxLayoutData
deriving instance ToExpr for GKRLayerDescription
deriving instance ToExpr for RegisterOnlyAccessAddress
deriving instance ToExpr for RegisterOrRamAddressSpace
deriving instance ToExpr for RegisterOrRamAccessAddress
deriving instance ToExpr for IndirectRamAccessAddress
deriving instance ToExpr for RamAddress
deriving instance ToExpr for RamReadQuery
deriving instance ToExpr for RamWriteQuery
deriving instance ToExpr for RamQuery
deriving instance ToExpr for GKRMachineState
deriving instance ToExpr for MachineStatePermutationDescription
deriving instance ToExpr for CompiledDelegationCircuitState
deriving instance ToExpr for DecoderPlacementDescription
deriving instance ToExpr for GKRMemoryLayout
deriving instance ToExpr for GKRWitnessLayout
deriving instance ToExpr for Degree1Constraint
deriving instance ToExpr for Degree2Constraint
deriving instance ToExpr for Airbender.Term
deriving instance ToExpr for Constraint
deriving instance ToExpr for Airbender.Expr
deriving instance ToExpr for StructuredStatement
deriving instance ToExpr for GKRCircuitArtifact

/-- A definition without code generation whose body importing modules can unfold (`forceExpose`). -/
def addTranscribedDef (name : Name) (type value : Lean.Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe }

/-- Share the capture placement array without changing its value. -/
def addSharedTranscribedDef (name : Name) (type value placementData : Lean.Expr)
    (sharingName : Name := name) : CoreM Unit := do
  let placementName := sharingName.appendAfter "PlacementEntries"
  let pairType := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``GKRAddress)
  addTranscribedDef placementName (mkApp (mkConst ``Array [0]) pairType) placementData
  let value := value.replace fun entry =>
    if entry == placementData then some (mkConst placementName) else none
  addTranscribedDef name type value

/-- Share literal array entries while retaining the complete kernel value. -/
def addTranscribedArray {α : Type} [ToExpr α] (name : Name) (entries : Array α) : CoreM Lean.Expr := do
  let type := toTypeExpr α
  let mut references : Array Lean.Expr := #[]
  for h : index in [0:entries.size] do
    let entryName := name.appendAfter s!"Entry{index}"
    addTranscribedDef entryName type (toExpr entries[index])
    references := references.push (mkConst entryName)
  let data := references.toList.foldr (mkApp3 (mkConst ``List.cons [0]) type)
    (mkApp (mkConst ``List.nil [0]) type)
  addTranscribedDef name (mkApp (mkConst ``Array [0]) type)
    (mkApp2 (mkConst ``Array.mk [0]) type data)
  return mkConst name

/-- Share large native gate and cache arrays and the placement array. -/
def addSharedCircuit (name sharingName : Name) (circuit : Circuit) : CoreM Unit := do
  let mut value := toExpr circuit
  for h : index in [0:circuit.layers.size] do
    let layer := circuit.layers[index]
    if layer.gates.size > 253 then
      let data ← addTranscribedArray (sharingName.appendAfter s!"Layer{index}Gates") layer.gates
      let original := toExpr layer.gates
      value := value.replace fun entry => if entry == original then some data else none
    if layer.cached_relations.size > 253 then
      let data ← addTranscribedArray (sharingName.appendAfter s!"Layer{index}Caches") layer.cached_relations
      let original := toExpr layer.cached_relations
      value := value.replace fun entry => if entry == original then some data else none
  addSharedTranscribedDef name (mkConst ``Circuit) value (toExpr circuit.placement_data.entries) sharingName

/-- Pairs of neighbours joined by `app`, in order. -/
def pairUp (app : Lean.Expr → Lean.Expr → Lean.Expr) : List Lean.Expr → List Lean.Expr
  | a :: b :: rest => app a b :: pairUp app rest
  | l => l

/-- One term joining all, by `app` in a balanced tree (`fuel` at least the list length). -/
def balanced (app : Lean.Expr → Lean.Expr → Lean.Expr) (empty : Lean.Expr) : Nat → List Lean.Expr → Lean.Expr
  | _, [] => empty
  | _, [e] => e
  | 0, e :: _ => e
  | fuel + 1, l => balanced app empty fuel (pairUp app l)

/-- `ByteArray.mk (Array.mk l)`, `l` the bytes as a balanced `List.append` tree of 256-byte lists: the kernel
    evaluates it without deep recursion (a flat list of a 19 KB file overflows it). -/
def bytesExpr (bytes : ByteArray) : Lean.Expr :=
  let u8 := mkConst ``UInt8
  let nil := mkApp (mkConst ``List.nil [0]) u8
  let leaf (bs : List UInt8) := bs.foldr (fun b acc => mkApp3 (mkConst ``List.cons [0]) u8 (toExpr b) acc) nil
  let leaves := (List.range ((bytes.size + 255) / 256)).map fun i =>
    leaf (bytes.data.extract (256 * i) (256 * i + 256)).toList
  let l := balanced (mkApp3 (mkConst ``List.append [0]) u8) nil leaves.length leaves
  mkApp (mkConst ``ByteArray.mk) (mkApp2 (mkConst ``Array.mk [0]) u8 l)

syntax (name := importCircuit) "import_circuit " ident " from " str (&" bytes")? (&" shared" ident)? : command

@[command_elab importCircuit]
def elabImportCircuit : CommandElab := fun stx => do
  let some path := stx[3].isStrLit? | throwUnsupportedSyntax
  let text ← IO.FS.readFile path
  let c ← match parseCircuit text with
    | .ok c => pure c
    | .error e => throwError "circuit import failed: {e}"
  let base := (← getCurrNamespace) ++ stx[1].getId
  liftCoreM do
    let bytesName := base.appendAfter "SourceBytes"
    let stringType := mkConst ``String
    addTranscribedDef bytesName stringType (mkStrLit text)
    compileDecl (.defnDecl
      { name := bytesName, levelParams := [], type := stringType, value := mkStrLit text, hints := .abbrev,
        safety := .safe })
    if stx[5].isNone then
      addTranscribedDef base (mkConst ``Circuit) (toExpr c)
    else
      addSharedCircuit base ((← getCurrNamespace) ++ stx[5][1].getId) c
    unless stx[4].isNone do
      addTranscribedDef (base.appendAfter "Bytes") (mkConst ``ByteArray) (bytesExpr text.toUTF8)

end Airbender

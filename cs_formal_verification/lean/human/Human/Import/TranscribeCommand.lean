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
responsibility. -/

namespace Airbender
open Lean Elab Command

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

syntax (name := importCircuit) "import_circuit " ident " from " str : command

@[command_elab importCircuit]
def elabImportCircuit : CommandElab := fun stx => do
  match stx with
  | `(import_circuit $name:ident from $path:str) => do
    let text ← IO.FS.readFile path.getString
    let c ← match parseCircuit text with
      | .ok c => pure c
      | .error e => throwError "circuit import failed: {e}"
    let base := (← getCurrNamespace) ++ name.getId
    liftCoreM do
      let bytesName := base.appendAfter "SourceBytes"
      let stringType := mkConst ``String
      addTranscribedDef bytesName stringType (mkStrLit text)
      compileDecl (.defnDecl
        { name := bytesName, levelParams := [], type := stringType, value := mkStrLit text, hints := .abbrev,
          safety := .safe })
      addTranscribedDef base (mkConst ``Circuit) (toExpr c)
  | _ => throwUnsupportedSyntax

end Airbender

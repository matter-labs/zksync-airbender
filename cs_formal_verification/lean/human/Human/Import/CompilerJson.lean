module
public import Human.Compiler.Capture
public meta import Human.Compiler.Capture
public meta import Human.Import.Schema
public meta import Human.Import.Json
public meta import Human.Import.BabyBear
public meta import Lean

public meta section

/-! Trusted JSON conversion for pinned compiler captures. The ordinary circuit decoder stays unchanged. -/

namespace Airbender
open Lean


instance : FromJson (BoundedNat bound) where
  fromJson? j := do
    let n ← j.getNat?
    if h : n < bound then return ⟨n, h⟩
    else throw s!"integer {n} must be less than {bound}"

instance : ToJson (BoundedNat bound) where
  toJson n := toJson n.val



instance [FromJson α] : FromJson (Fixed n α) where
  fromJson? j := do
    let values : Array α ← fromJson? j
    if h : values.size = n then return ⟨values, h⟩
    else throw s!"expected array of length {n}, got {values.size}"

instance [ToJson α] : ToJson (Fixed n α) where
  toJson a := toJson a.values


instance [FromJson α] [FromJson β] [FromJson γ] : FromJson (Triple α β γ) where
  fromJson? j := do
    let a ← j.getArr?
    if a.size != 3 then throw "expected a three-element tuple"
    return ⟨← fromJson? a[0]!, ← fromJson? a[1]!, ← fromJson? a[2]!⟩

instance [ToJson α] [ToJson β] [ToJson γ] : ToJson (Triple α β γ) where
  toJson t := .arr #[toJson t.first, toJson t.second, toJson t.third]

class NativeObjectKey (κ : Type) where
  /-- Decode the native map key. -/
  decode : String → Except String κ
  /-- Encode the native map key. -/
  encode : κ → String
  /-- Order keys as the native Rust BTree map. -/
  rank : κ → Nat

instance : NativeObjectKey Nat where
  decode s := match s.toNat? with
    | some n => .ok n
    | none => .error "expected a natural-number object key"
  encode := toString
  rank := id


instance [NativeObjectKey κ] [FromJson α] : FromJson (ObjectMap κ α) where
  fromJson? j := do
    let obj ← j.getObj?
    let entries ← obj.toArray.mapM fun (key, value) => do
      return (← NativeObjectKey.decode key, ← fromJson? value)
    return ⟨entries.qsort (fun a b => NativeObjectKey.rank a.1 < NativeObjectKey.rank b.1)⟩

instance [NativeObjectKey κ] [ToJson α] : ToJson (ObjectMap κ α) where
  toJson m := Json.mkObj <| m.entries.toList.map fun (key, value) =>
    (NativeObjectKey.encode key, toJson value)


instance : FromJson JsonNull where
  fromJson? j := if j == .null then .ok .null else .error "expected null"

instance : ToJson JsonNull where
  toJson _ := .null



instance : FromJson Coefficient where
  fromJson? value := Coefficient.mk <$> fromJson? value

instance : ToJson Coefficient where
  toJson value := toJson value.raw

deriving instance FromJson, ToJson for ColumnRange
deriving instance FromJson, ToJson for OutputType

instance : NativeObjectKey OutputType where
  decode key := fromJson? (.str key)
  encode value := (toJson value).getStr?.toOption.getD ""
  rank
    | .PermutationProduct => 0
    | .Lookup16Bits => 1
    | .LookupTimestamps => 2
    | .GenericLookup => 3
    | .InitsAndTeardownsProduct => 4

deriving instance FromJson, ToJson for VirtualSetupPoly
deriving instance FromJson, ToJson for GKRAddress
deriving instance FromJson, ToJson for LinearRelation
deriving instance FromJson, ToJson for SingleColumnLookupRelation
deriving instance FromJson, ToJson for VectorLookupRelation
deriving instance FromJson, ToJson for CompiledMaxQuadraticGKRRelation
deriving instance FromJson, ToJson for CompiledAddressSpaceRelationStrict
deriving instance FromJson, ToJson for CompiledAddressStrict
deriving instance FromJson, ToJson for CompiledMemoryTimestamp
deriving instance FromJson, ToJson for RamWordRepresentation
deriving instance FromJson, ToJson for SpecialMemoryContributionRelation
deriving instance FromJson, ToJson for MaxQuadraticConstraintsGKRRelation
deriving instance FromJson, ToJson for InitsOrTeardownsTimestampAndValue
deriving instance FromJson, ToJson for StructuredExpression
deriving instance FromJson, ToJson for GKRRelation
deriving instance FromJson, ToJson for GKRCacheRelation
deriving instance FromJson, ToJson for GateArtifacts
deriving instance FromJson, ToJson for RamAuxComparisonSet
deriving instance FromJson, ToJson for RelativeTimestampGroup
deriving instance FromJson, ToJson for GKRAuxLayoutData
deriving instance FromJson, ToJson for GKRLayerDescription
deriving instance FromJson, ToJson for RegisterOnlyAccessAddress
deriving instance FromJson, ToJson for RegisterOrRamAddressSpace
deriving instance FromJson, ToJson for RegisterOrRamAccessAddress
deriving instance FromJson, ToJson for IndirectRamAccessAddress
deriving instance FromJson, ToJson for RamAddress
deriving instance FromJson, ToJson for RamReadQuery
deriving instance FromJson, ToJson for RamWriteQuery
deriving instance FromJson, ToJson for RamQuery
deriving instance FromJson, ToJson for GKRMachineState
deriving instance FromJson, ToJson for MachineStatePermutationDescription
deriving instance FromJson, ToJson for CompiledDelegationCircuitState
deriving instance FromJson, ToJson for DecoderPlacementDescription
deriving instance FromJson, ToJson for GKRMemoryLayout
deriving instance FromJson, ToJson for GKRWitnessLayout
deriving instance FromJson, ToJson for Degree1Constraint
deriving instance FromJson, ToJson for Degree2Constraint
deriving instance FromJson, ToJson for Term
deriving instance FromJson, ToJson for Constraint
deriving instance FromJson, ToJson for Expr
deriving instance FromJson, ToJson for StructuredStatement
deriving instance FromJson, ToJson for GKRCircuitArtifact

deriving instance FromJson for Compiler.RemainingInputs
deriving instance FromJson for Compiler.SourceSnapshot
deriving instance FromJson for Compiler.NativeCapture

end Airbender

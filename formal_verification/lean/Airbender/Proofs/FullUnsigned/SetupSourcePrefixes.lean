import Airbender.Proofs.FullUnsigned.SourceIndexSlices
import Airbender.Proofs.FullUnsigned.SetupSourceCertificate

namespace Airbender.Setup.SourceBankCertificate
open Lean Meta Elab Command
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- A bounded prefix follows from its original source-index encoding. -/
theorem take_encoded (entries : List Nat) (radix count rest packed : Nat) (retained : List Nat)
    (encoded : entries = SourceIndices.decode radix (count + rest) packed)
    (checked : SourceIndices.decode radix count packed = retained) : entries.take count = retained := by
  rw [encoded, SourceIndices.decode_take, checked]

private partial def unfoldEntries (value : Lean.Expr) : MetaM Lean.Expr := do
  if value.isAppOf ``SourceIndices.decode then return value
  if value.getAppFn.isConst then
    if let .defnInfo info ← getConstInfo value.getAppFn.constName! then
      return ← unfoldEntries ((mkAppN info.value value.getAppArgs).headBeta)
  return value

private partial def metadataElements (value : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let value ← whnf value
  if value.isAppOf ``List.nil then return #[]
  unless value.isAppOf ``List.cons do throwError "expected source metadata"
  let args := value.getAppArgs
  return #[args[1]!] ++ (← metadataElements args[2]!)

private def storedNat (value : Lean.Expr) : MetaM Nat := do
  let value ← whnf value
  if let .lit (.natVal n) := value then return n
  if value.isAppOf ``OfNat.ofNat then
    if let .lit (.natVal n) := value.getAppArgs[1]! then return n
  throwError "expected a stored natural value"

private def natList (values : List Nat) : Lean.Expr :=
  values.foldr (fun value rest =>
    mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Nat) (mkRawNatLit value) rest)
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat))

/-- Propose a short source prefix. Ordinary kernel conversion checks every
stored index and the application of the prefix theorem. -/
elab "certify_source_prefix " target:ident " from " source:ident " prefix_count " count:num : command =>
    withEnableInfoTree false do
  let sourceName ← resolveGlobalConstNoOverload source
  let sourceExpr := mkConst sourceName
  let decoded ← liftTermElabM <| unfoldEntries sourceExpr
  let (values, makeProof) ← liftTermElabM do
    if decoded.isAppOf ``SourceIndices.decode then
      let args := decoded.getAppArgs
      let radix ← storedNat args[0]!
      let total ← storedNat args[1]!
      let packed ← storedNat args[2]!
      unless 0 < radix && count.getNat ≤ total do throwError "invalid source prefix"
      let values := (List.range count.getNat).map fun index => (packed / radix ^ index) % radix
      let encoded ← mkEqRefl sourceExpr
      let small := mkAppN (mkConst ``SourceIndices.decode)
        #[mkRawNatLit radix, mkRawNatLit count.getNat, mkRawNatLit packed]
      let checked ← mkEqRefl small
      return (values, fun retained => mkAppN (mkConst ``take_encoded)
        #[sourceExpr, mkRawNatLit radix, mkRawNatLit count.getNat, mkRawNatLit (total - count.getNat),
          mkRawNatLit packed, retained, encoded, checked])
    else
      let all ← metadataElements sourceExpr
      unless count.getNat ≤ all.size do throwError "source prefix is too long"
      let values ← ((all.toList.take count.getNat).mapM storedNat : MetaM (List Nat))
      let selected ← mkAppM ``List.take #[mkRawNatLit count.getNat, sourceExpr]
      let checked ← mkEqRefl selected
      return (values, fun _ => checked)
  let entriesName := target.getId.str "entries"
  let value := natList values
  let type := mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)
  let height := getMaxHeight (← getEnv) value + 1
  liftCoreM <| addDecl (.defnDecl {
    name := entriesName, levelParams := [], type := type, value := value,
    hints := .regular height, safety := .safe })
  modifyEnv (addNoncomputable · entriesName)
  let selected ← liftTermElabM <| mkAppM ``List.take #[mkRawNatLit count.getNat, sourceExpr]
  let type ← liftTermElabM <| mkEq selected (mkConst entriesName)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDecl (.thmDecl {
      name := target.getId.str "matches", levelParams := [], type := type,
      value := makeProof (mkConst entriesName) })

end Airbender.Setup.SourceBankCertificate

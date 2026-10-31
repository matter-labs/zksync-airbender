import Airbender.Proofs.FullUnsigned.SourceIndexSlices
import Airbender.Proofs.FullUnsigned.SetupSourceCertificate

namespace Airbender.Setup.SourceIndices
set_option warningAsError true
set_option Elab.async false

theorem decode_split (radix first rest packed : Nat) :
    decode radix (first + rest) packed =
      decode radix first (packed % radix ^ first) ++ decode radix rest (packed / radix ^ first) := by
  calc
    _ = (decode radix (first + rest) packed).take first ++
        (decode radix (first + rest) packed).drop first := (List.take_append_drop first _).symm
    _ = _ := by rw [decode_take, decode_mod, decode_drop]

/-- Exact scalar splits compose the original encoded source-index sequence. -/
theorem partition_join (radix first rest packed power low high : Nat)
    (left right : List (List Nat)) (powerEq : Nat.pow radix first = power)
    (lowEq : packed % power = low) (highEq : packed / power = high)
    (a : decode radix first low = left.flatten) (b : decode radix rest high = right.flatten) :
    decode radix (first + rest) packed = (left ++ right).flatten := by
  simp only [Nat.pow_eq] at powerEq
  rw [decode_split, powerEq, lowEq, highEq, a, b, List.flatten_append]

theorem singleton_partition (entries : List Nat) : entries = [entries].flatten := by simp

open Lean Meta Elab Command
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem power_zero (radix : Nat) : Nat.pow radix 0 = 1 := rfl
private theorem power_even (radix total half value result : Nat)
    (totalEq : total = half + half) (previous : Nat.pow radix half = value)
    (product : value * value = result) : Nat.pow radix total = result := by
  simp only [Nat.pow_eq] at previous ⊢
  rw [totalEq, Nat.pow_add, previous, product]
private theorem power_odd (radix total half value result : Nat)
    (totalEq : total = half + half + 1) (previous : Nat.pow radix half = value)
    (product : value * value * radix = result) : Nat.pow radix total = result := by
  simp only [Nat.pow_eq] at previous ⊢
  rw [totalEq, Nat.pow_succ, Nat.pow_add, previous, product]

private partial def binaryPower (radix count : Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  if count = 0 then return (mkRawNatLit 1, mkApp (mkConst ``power_zero) (mkRawNatLit radix))
  let (value, previous) ← binaryPower radix (count / 2)
  let square ← mkAppM ``Nat.mul #[value, value]
  let totalEq ← mkEqRefl (mkRawNatLit count)
  if count % 2 = 0 then
    let product ← mkEqRefl square
    let result := mkRawNatLit ((value.rawNatLit?.getD 0) * (value.rawNatLit?.getD 0))
    return (result, mkAppN (mkConst ``power_even) #[mkRawNatLit radix, mkRawNatLit count,
      mkRawNatLit (count / 2), value, result, totalEq, previous, product])
  else
    let productValue ← mkAppM ``Nat.mul #[square, mkRawNatLit radix]
    let product ← mkEqRefl productValue
    let result := mkRawNatLit ((value.rawNatLit?.getD 0) * (value.rawNatLit?.getD 0) * radix)
    return (result, mkAppN (mkConst ``power_odd) #[mkRawNatLit radix, mkRawNatLit count,
      mkRawNatLit (count / 2), value, result, totalEq, previous, product])

private partial def unfoldEntries (value : Lean.Expr) : MetaM Lean.Expr := do
  if value.isAppOf ``decode then return value
  if value.getAppFn.isConst then
    if let .defnInfo info ← getConstInfo value.getAppFn.constName! then
      return ← unfoldEntries ((mkAppN info.value value.getAppArgs).headBeta)
  return value
private def storedNat (value : Lean.Expr) : MetaM Nat := do
  let value ← whnf value
  if let .lit (.natVal n) := value then return n
  if value.isAppOf ``OfNat.ofNat then
    if let .lit (.natVal n) := value.getAppArgs[1]! then return n
  throwError "expected source scalar metadata"
private def listExpr (type : Lean.Expr) (values : Array Lean.Expr) : Lean.Expr :=
  values.foldr (fun value rest => mkApp3 (mkConst ``List.cons [Level.zero]) type value rest)
    (mkApp (mkConst ``List.nil [Level.zero]) type)
private def checkedData (name : Name) (type value : Lean.Expr) : CommandElabM Unit := do
  let height := getMaxHeight (← getEnv) value + 1
  liftCoreM <| addDecl (.defnDecl {
    name := name, levelParams := [], type := type, value := value,
    hints := .regular height, safety := .safe })
  modifyEnv (addNoncomputable · name)
private def checkedProof (name : Name) (type value : Lean.Expr) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := name, levelParams := [], type := type, value := value })

private partial def buildPartition (target : Name) (radix : Nat) (counts : Array Nat)
    (first : Nat) (packed : Nat) : CommandElabM (Lean.Expr × Lean.Expr) := do
  let natListType := mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)
  let total := counts.foldl (· + ·) 0
  let decoded := mkAppN (mkConst ``decode) #[mkRawNatLit radix, mkRawNatLit total, mkRawNatLit packed]
  if counts.size = 1 then
    let name := target.str s!"chunk_{first}"
    checkedData name natListType decoded
    let parts := listExpr natListType #[mkConst name]
    let proof := mkApp (mkConst ``singleton_partition) (mkConst name)
    return (parts, proof)
  let half := counts.size / 2
  let leftCounts := counts.extract 0 half
  let rightCounts := counts.extract half counts.size
  let leftSize := leftCounts.foldl (· + ·) 0
  let rightSize := rightCounts.foldl (· + ·) 0
  let power := radix ^ leftSize
  let low := packed % power
  let high := packed / power
  let (left, a) ← buildPartition target radix leftCounts first low
  let (right, b) ← buildPartition target radix rightCounts (first + half) high
  let (powerExpr, powerProof) ← liftTermElabM <| binaryPower radix leftSize
  let lowExpr := mkApp2 (mkConst ``Nat.mod) (mkRawNatLit packed) powerExpr
  let highExpr := mkApp2 (mkConst ``Nat.div) (mkRawNatLit packed) powerExpr
  let lowProof ← liftTermElabM <| mkEqRefl lowExpr
  let highProof ← liftTermElabM <| mkEqRefl highExpr
  let proof := mkAppN (mkConst ``partition_join) #[mkRawNatLit radix, mkRawNatLit leftSize,
    mkRawNatLit rightSize, mkRawNatLit packed, powerExpr, mkRawNatLit low, mkRawNatLit high,
    left, right, powerProof, lowProof, highProof, a, b]
  let parts ← liftTermElabM <| mkAppM ``List.append #[left, right]
  let flattened ← liftTermElabM <| mkAppM ``List.flatten #[parts]
  let type ← liftTermElabM <| mkEq decoded flattened
  let name := mkPrivateNameCore (← getEnv).mainModule (target.str s!"node_{first}_{counts.size}")
  checkedProof name type proof
  return (parts, mkConst name)

/-- Propose a balanced partition of actual encoded source indices. Each scalar
split and each proof application enters the ordinary kernel. -/
elab "certify_source_partition " target:ident " from " source:ident
    " chunk_counts " "[" counts:num,* "]" : command => withEnableInfoTree false do
  let sourceName ← resolveGlobalConstNoOverload source
  let sourceExpr := mkConst sourceName
  let encoded ← liftTermElabM <| unfoldEntries sourceExpr
  unless encoded.isAppOf ``decode do throwError "expected an encoded source-index list"
  let args := encoded.getAppArgs
  let radix ← liftTermElabM <| storedNat args[0]!
  let total ← liftTermElabM <| storedNat args[1]!
  let packed ← liftTermElabM <| storedNat args[2]!
  let counts := counts.getElems.map (·.getNat)
  unless counts.size > 0 && counts.all (0 < ·) && counts.foldl (· + ·) 0 = total && radix > 0 do
    throwError "invalid complete source partition"
  let (parts, proof) ← buildPartition target.getId radix counts 0 packed
  let type ← liftTermElabM <| inferType parts
  let partsName := target.getId.str "chunks"
  checkedData partsName type parts
  let flattened ← liftTermElabM <| mkAppM ``List.flatten #[mkConst partsName]
  let type ← liftTermElabM <| mkEq sourceExpr flattened
  checkedProof (target.getId.str "matches") type proof

end Airbender.Setup.SourceIndices
